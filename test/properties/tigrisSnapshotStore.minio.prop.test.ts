import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { afterAll, beforeAll, describe, expect } from 'vitest';
import { S3Client } from '@aws-sdk/client-s3';
import { ManifestFile } from '../../src/core/compaction';
import { SqlSchema } from '../../src/core/sql';
import { TigrisSnapshotStore } from '../../src/backend/tigrisSnapshotStore';
import { MinioHarness } from '../e2e/minioHarness';

const numRuns = Number(process.env.MINIO_PROP_NUM_RUNS ?? 12);
const timeoutMs = Number(process.env.MINIO_PROP_TIMEOUT_MS ?? 120_000);

function manifestForVersion(version: number): ManifestFile {
  return {
    v: 1,
    version,
    compaction_hlc: '0x0',
    segments: [],
    sites_compacted: {},
  };
}

const arbIdentifier = fc.stringMatching(/^[a-z][a-z0-9_]{0,10}$/u);
const arbSchema: fc.Arbitrary<SqlSchema> = fc.dictionary(
  arbIdentifier,
  fc.constant({
    pk: 'id',
    partitionBy: null,
    columns: {
      id: { crdt: 'scalar' as const },
      title: { crdt: 'lww' as const },
      points: { crdt: 'pn_counter' as const },
      tags: { crdt: 'or_set' as const },
      status: { crdt: 'mv_register' as const },
    },
  }),
  { maxKeys: 5 },
);

describe('TigrisSnapshotStore properties (MinIO)', () => {
  let tempRoot: string | null = null;
  let minio: MinioHarness | null = null;
  let sharedS3Client: S3Client | null = null;
  let runPrefixRoot = '';

  beforeAll(async () => {
    tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-snapshot-minio-prop-'));
    minio = await MinioHarness.start({
      rootDir: tempRoot,
      bucket: 'crdtbase-snapshots',
    });
    sharedS3Client = new S3Client(minio.getS3ClientConfig());
    runPrefixRoot = `props-${Date.now().toString(36)}`;
  }, timeoutMs);

  afterAll(async () => {
    if (sharedS3Client) {
      sharedS3Client.destroy();
      sharedS3Client = null;
    }
    if (minio) {
      await minio.stop();
      minio = null;
    }
    if (tempRoot) {
      await rm(tempRoot, { recursive: true, force: true });
      tempRoot = null;
    }
  });

  test.prop([fc.nat({ max: 8 }), fc.nat({ max: 8 }), fc.uuid()], { numRuns })(
    'manifest CAS succeeds iff expected version equals current version',
    async (currentVersion, expectedVersion, suffix) => {
      const store = new TigrisSnapshotStore({
        bucket: minio!.getBucket(),
        prefix: `${runPrefixRoot}/cas-${suffix}`,
        client: sharedS3Client!,
      });

      for (let version = 1; version <= currentVersion; version += 1) {
        const seeded = await store.putManifest(manifestForVersion(version), version - 1);
        expect(seeded).toBe(true);
      }

      const applied = await store.putManifest(
        manifestForVersion(expectedVersion + 1),
        expectedVersion,
      );
      const shouldApply = expectedVersion === currentVersion;
      expect(applied).toBe(shouldApply);

      const finalManifest = await store.getManifest();
      const finalVersion = finalManifest?.version ?? 0;
      expect(finalVersion).toBe(shouldApply ? expectedVersion + 1 : currentVersion);
    },
    timeoutMs,
  );

  test.prop([fc.uint8Array({ maxLength: 2048 }), arbIdentifier, fc.uuid()], { numRuns })(
    'segment bytes round-trip through MinIO-backed store',
    async (bytes, table, suffix) => {
      const store = new TigrisSnapshotStore({
        bucket: minio!.getBucket(),
        prefix: `${runPrefixRoot}/segments-${suffix}`,
        client: sharedS3Client!,
      });
      const path = `segments/${table}_default.seg.bin`;
      await store.putSegment(path, bytes);
      const loaded = await store.getSegment(path);
      expect(loaded).not.toBeNull();
      expect(loaded).toEqual(bytes);
    },
    timeoutMs,
  );

  test.prop([arbSchema, fc.uuid()], { numRuns })(
    'schema round-trips through MinIO-backed store',
    async (schema, suffix) => {
      const store = new TigrisSnapshotStore({
        bucket: minio!.getBucket(),
        prefix: `${runPrefixRoot}/schema-${suffix}`,
        client: sharedS3Client!,
      });
      await store.putSchema(schema);
      const loaded = await store.getSchema();
      expect(loaded).toEqual(schema);
    },
    timeoutMs,
  );
});
