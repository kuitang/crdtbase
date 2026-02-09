import { execFile as execFileWithCallback } from 'node:child_process';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { GetObjectCommand, ListObjectsV2Command, S3Client } from '@aws-sdk/client-s3';
import { afterEach, describe, expect, it } from 'vitest';
import { S3ReplicatedLog } from '../../src/backend/s3ReplicatedLog';
import { TigrisSnapshotStore } from '../../src/backend/tigrisSnapshotStore';
import { decodeBin } from '../../src/core/encoding';
import { SqlSchema } from '../../src/core/sql';
import { compactReplicatedLog } from '../../src/platform/node/compactor';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import { MinioHarness } from './minioHarness';
import { E2E_SCHEDULES, TASK_QUERY_SQL, runThreeClientConvergenceScenario } from './orchestrator';

const execFile = promisify(execFileWithCallback);

async function objectBodyToBytes(body: unknown): Promise<Uint8Array> {
  if (!body) {
    throw new Error('missing object body');
  }
  const streamBody = body as { transformToByteArray?: () => Promise<Uint8Array> };
  if (typeof streamBody.transformToByteArray === 'function') {
    return streamBody.transformToByteArray();
  }
  throw new Error('unsupported object body type');
}

describe('S3 ReplicatedLog with MinIO', () => {
  let tempRoot: string | null = null;
  let minio: MinioHarness | null = null;

  afterEach(async () => {
    if (minio) {
      await minio.stop();
      minio = null;
    }
    if (tempRoot) {
      await rm(tempRoot, { recursive: true, force: true });
      tempRoot = null;
    }
  });

  it.each(E2E_SCHEDULES)(
    'syncs 3 SQL clients directly through S3 and inspects downloaded .bin files with dump [$name]',
    async (schedule) => {
      tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-minio-e2e-'));
      minio = await MinioHarness.start({
        rootDir: tempRoot,
        bucket: 'crdtbase',
      });

      const s3Config = minio.getS3ClientConfig();
      const bucket = minio.getBucket();
      const clientADir = join(tempRoot, 'client-a');
      const clientBDir = join(tempRoot, 'client-b');
      const clientCDir = join(tempRoot, 'client-c');
      const clientDDir = join(tempRoot, 'client-d');

      const logA = new S3ReplicatedLog({
        bucket,
        prefix: 'deltas',
        clientConfig: s3Config,
      });
      const logB = new S3ReplicatedLog({
        bucket,
        prefix: 'deltas',
        clientConfig: s3Config,
      });
      const logC = new S3ReplicatedLog({
        bucket,
        prefix: 'deltas',
        clientConfig: s3Config,
      });

      const clientA = await NodeCrdtClient.open({
        siteId: 'site-a',
        log: logA,
        dataDir: clientADir,
        now: () => 1_000,
      });
      const clientB = await NodeCrdtClient.open({
        siteId: 'site-b',
        log: logB,
        dataDir: clientBDir,
        now: () => 2_000,
      });
      const clientC = await NodeCrdtClient.open({
        siteId: 'site-c',
        log: logC,
        dataDir: clientCDir,
        now: () => 3_000,
      });

      const result = await runThreeClientConvergenceScenario({
        clients: {
          'site-a': clientA,
          'site-b': clientB,
          'site-c': clientC,
        },
        schedule,
      });
      const rowsA = result.rowsBySite['site-a'];
      const rowsB = result.rowsBySite['site-b'];
      const rowsC = result.rowsBySite['site-c'];
      expect(rowsA).toEqual(rowsB);
      expect(rowsB).toEqual(rowsC);
      expect(rowsA).toHaveLength(1);

      const row = rowsA[0]!;
      expect(row.id).toBe('t1');
      expect(row.title).toBe('from-c');
      expect(row.points).toBe(8);
      expect(new Set(row.tags as string[])).toEqual(new Set(['beta', 'gamma']));
      expect(row.status).toEqual(['open', 'review']);

      const rawS3Client = new S3Client(s3Config);
      const listResp = await rawS3Client.send(
        new ListObjectsV2Command({
          Bucket: bucket,
          Prefix: 'deltas/',
        }),
      );
      const keys = (listResp.Contents ?? [])
        .flatMap((item) => (item.Key ? [item.Key] : []))
        .sort();

      expect(keys).toEqual([
        'deltas/site-a/0000000001.delta.bin',
        'deltas/site-b/0000000001.delta.bin',
        'deltas/site-b/0000000002.delta.bin',
        'deltas/site-c/0000000001.delta.bin',
      ]);

      const downloadDir = join(tempRoot, 'downloads');
      await mkdir(downloadDir, { recursive: true });

      for (const key of keys) {
        const object = await rawS3Client.send(
          new GetObjectCommand({
            Bucket: bucket,
            Key: key,
          }),
        );
        const bytes = await objectBodyToBytes(object.Body);
        const localFile = join(downloadDir, key.replaceAll('/', '__'));
        await writeFile(localFile, bytes);
        const dumped = await execFile('node', ['cli.mjs', 'dump', localFile], {
          cwd: process.cwd(),
        });
        const decoded = JSON.parse(dumped.stdout) as {
          siteId: string;
          seq: number;
          ops: unknown[];
        };
        expect(decoded.siteId.startsWith('site-')).toBe(true);
        expect(decoded.seq).toBeGreaterThanOrEqual(1);
        expect(Array.isArray(decoded.ops)).toBe(true);
      }

      // Double-check one downloaded file is readable as bytes in harness output directory.
      const samplePath = join(downloadDir, 'deltas__site-b__0000000001.delta.bin');
      const sampleBytes = await readFile(samplePath);
      expect(sampleBytes.length).toBeGreaterThan(0);

      const snapshots = new TigrisSnapshotStore({
        bucket,
        prefix: 'snapshots',
        clientConfig: s3Config,
      });
      const schemaBytes = await readFile(join(clientADir, 'schema.bin'));
      const schema = decodeBin<SqlSchema>(schemaBytes);
      await snapshots.putSchema(schema);

      const compaction = await compactReplicatedLog({
        log: logA,
        schema,
        snapshots,
      });
      expect(compaction.applied).toBe(true);
      expect(compaction.opsRead).toBe(12);
      expect(compaction.manifest.segments).toHaveLength(1);
      expect(compaction.manifest.sites_compacted).toEqual({
        'site-a': 1,
        'site-b': 2,
        'site-c': 1,
      });

      const logD = new S3ReplicatedLog({
        bucket,
        prefix: 'deltas',
        clientConfig: s3Config,
      });
      const clientD = await NodeCrdtClient.open({
        siteId: 'site-d',
        log: logD,
        dataDir: clientDDir,
        snapshots,
        now: () => 4_000,
      });
      await clientD.pull();
      const rowsD = await clientD.query(TASK_QUERY_SQL);
      expect(rowsD).toEqual(rowsA);

      const snapshotList = await rawS3Client.send(
        new ListObjectsV2Command({
          Bucket: bucket,
          Prefix: 'snapshots/',
        }),
      );
      const snapshotKeys = (snapshotList.Contents ?? [])
        .flatMap((item) => (item.Key ? [item.Key] : []))
        .sort();
      expect(snapshotKeys).toContain('snapshots/manifest.bin');
      expect(snapshotKeys).toContain('snapshots/schema.bin');
      expect(
        snapshotKeys.some((key) =>
          key.startsWith('snapshots/segments/'),
        ),
      ).toBe(true);

      const secondCompaction = await compactReplicatedLog({
        log: logA,
        schema,
        snapshots,
      });
      expect(secondCompaction.applied).toBe(true);
      expect(secondCompaction.opsRead).toBe(0);
      expect(secondCompaction.manifest.sites_compacted).toEqual(compaction.manifest.sites_compacted);
      rawS3Client.destroy();
    },
    120_000,
  );
});
