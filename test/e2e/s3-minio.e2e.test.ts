import { execFile as execFileWithCallback } from 'node:child_process';
import { mkdtemp, mkdir, readFile, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { GetObjectCommand, ListObjectsV2Command, S3Client } from '@aws-sdk/client-s3';
import { afterEach, describe, expect, it } from 'vitest';
import { TigrisSnapshotStore } from '../../src/backend/tigrisSnapshotStore';
import { decodeBin } from '../../src/core/encoding';
import { SqlSchema } from '../../src/core/sql';
import { compactReplicatedLog } from '../../src/platform/node/compactor';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import {
  HttpS3PresignProvider,
  PresignedS3ReplicatedLog,
} from '../../src/platform/shared/presignedS3ReplicatedLog';
import { MinioHarness } from './minioHarness';
import { PresignHarness } from './presignHarness';
import {
  normalizeTaskRows,
  runThreeClientChaosScenario,
} from './orchestrator';
import { assertAckedWritesVisible, loadChaosEnv } from './chaosShared';

const execFile = promisify(execFileWithCallback);
const CHAOS = loadChaosEnv();

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

describe('S3 pre-signed replication over MinIO chaos', () => {
  let tempRoot: string | null = null;
  let minio: MinioHarness | null = null;
  let presign: PresignHarness | null = null;

  afterEach(async () => {
    if (presign) {
      await presign.stop();
      presign = null;
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

  it.each(CHAOS.seeds)(
    'converges under random delayed concurrent client activity through pre-signed S3 transport [seed=%s]',
    async (seed) => {
      tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-minio-chaos-e2e-'));
      minio = await MinioHarness.start({
        rootDir: tempRoot,
        bucket: 'crdtbase',
      });
      presign = await PresignHarness.start({
        endpoint: minio.getEndpoint(),
      });

      const s3Config = minio.getS3ClientConfig();
      const bucket = minio.getBucket();
      const clientADir = join(tempRoot, 'client-a');
      const clientBDir = join(tempRoot, 'client-b');
      const clientCDir = join(tempRoot, 'client-c');
      const observerDir = join(tempRoot, 'observer');
      const clientDDir = join(tempRoot, 'client-d');

      const provider = new HttpS3PresignProvider({
        baseUrl: presign.getBaseUrl(),
      });
      const makeLog = (): PresignedS3ReplicatedLog =>
        new PresignedS3ReplicatedLog({
          bucket,
          prefix: 'deltas',
          presign: provider,
        });

      const logA = makeLog();
      const logB = makeLog();
      const logC = makeLog();

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
      const observer = await NodeCrdtClient.open({
        siteId: 'site-observer',
        log: makeLog(),
        dataDir: observerDir,
        now: () => 3_500,
      });

      const result = await runThreeClientChaosScenario({
        clients: {
          'site-a': clientA,
          'site-b': clientB,
          'site-c': clientC,
        },
        observer,
        config: {
          seed,
          stepsPerClient: CHAOS.steps,
          maxDelayMs: CHAOS.maxDelayMs,
          drainRounds: CHAOS.drainRounds,
          quiescenceRounds: CHAOS.quiescenceRounds,
        },
      });

      const rowsA = result.normalizedRowsBySite['site-a'];
      const rowsB = result.normalizedRowsBySite['site-b'];
      const rowsC = result.normalizedRowsBySite['site-c'];

      expect(rowsA).toEqual(rowsB);
      expect(rowsB).toEqual(rowsC);
      expect(rowsA.length).toBeGreaterThan(0);
      expect(result.observerRows).toEqual(rowsA);
      expect(result.convergenceRound).toBeGreaterThan(0);
      expect(result.stats.writes).toBeGreaterThan(0);

      assertAckedWritesVisible({
        rows: rowsA,
        expectedPointsByRow: result.expectedPointsByRow,
        expectedTagsByRow: result.expectedTagsByRow,
      });

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

      expect(keys.length).toBeGreaterThan(0);
      expect(keys.some((key) => key.startsWith('deltas/site-a/'))).toBe(true);
      expect(keys.some((key) => key.startsWith('deltas/site-b/'))).toBe(true);
      expect(keys.some((key) => key.startsWith('deltas/site-c/'))).toBe(true);

      const downloadDir = join(tempRoot, 'downloads');
      await mkdir(downloadDir, { recursive: true });

      const sampleKeys = keys.slice(0, Math.min(keys.length, 8));
      for (const key of sampleKeys) {
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
        expect(decoded.ops.length).toBeGreaterThan(0);
      }

      const samplePath = join(downloadDir, sampleKeys[0]!.replaceAll('/', '__'));
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
      expect(compaction.opsRead).toBeGreaterThan(0);
      expect(compaction.manifest.segments.length).toBeGreaterThan(0);
      expect(compaction.manifest.sites_compacted['site-a']).toBe(await logA.getHead('site-a'));
      expect(compaction.manifest.sites_compacted['site-b']).toBe(await logA.getHead('site-b'));
      expect(compaction.manifest.sites_compacted['site-c']).toBe(await logA.getHead('site-c'));

      const logD = makeLog();
      const clientD = await NodeCrdtClient.open({
        siteId: 'site-d',
        log: logD,
        dataDir: clientDDir,
        snapshots,
        now: () => 4_000,
      });
      await clientD.pull();
      const rowsD = normalizeTaskRows(await clientD.query('SELECT * FROM tasks;'));
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
      expect(snapshotKeys.some((key) => key.startsWith('snapshots/segments/'))).toBe(true);

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
