import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { ListObjectsV2Command, S3Client } from '@aws-sdk/client-s3';
import { afterAll, afterEach, beforeAll, describe, expect, it } from 'vitest';
import type { Browser, BrowserContext } from 'playwright-core';
import { S3ReplicatedLog } from '../../src/backend/s3ReplicatedLog';
import { assertAckedWritesVisible, loadChaosEnv } from './chaosShared';
import { MinioHarness } from './minioHarness';
import { runThreeClientChaosScenario } from './orchestrator';
import {
  buildBrowserBridgeBundle,
  createBrowserS3Adapter,
  destroyBrowserAdapters,
  launchPlaywrightBrowser,
} from './playwrightBrowserHarness';

describe('Browser x S3-MinIO direct transport chaos end-to-end sync', () => {
  const CHAOS = loadChaosEnv();
  let browser: Browser | null = null;
  let bridgeBundle = '';

  let tempRoot: string | null = null;
  let minio: MinioHarness | null = null;
  let context: BrowserContext | null = null;

  beforeAll(async () => {
    bridgeBundle = await buildBrowserBridgeBundle();
    browser = await launchPlaywrightBrowser();
  }, 120_000);

  afterAll(async () => {
    if (browser) {
      await browser.close();
      browser = null;
    }
  });

  afterEach(async () => {
    if (context) {
      await context.close();
      context = null;
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
    'converges under random delayed concurrent browser activity through direct S3 transport [seed=%s]',
    async (seed) => {
      if (!browser) {
        throw new Error('browser is not started');
      }

      tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-browser-s3-chaos-'));
      minio = await MinioHarness.start({
        rootDir: tempRoot,
        bucket: 'crdtbase',
      });

      const s3Config = minio.getS3ClientConfig();
      const bucket = minio.getBucket();
      const endpoint = minio.getEndpoint();
      const pageUrl = `${endpoint}/minio/health/ready`;

      context = await browser.newContext();

      const clientA = await createBrowserS3Adapter({
        context,
        bridgeBundle,
        siteId: 'site-a',
        clientId: `site-a-${seed}`,
        pageUrl,
        bucket,
        prefix: 'deltas',
        endpoint: s3Config.endpoint,
        region: s3Config.region,
        accessKeyId: s3Config.credentials.accessKeyId,
        secretAccessKey: s3Config.credentials.secretAccessKey,
        forcePathStyle: true,
        nowMs: 1_000,
      });
      const clientB = await createBrowserS3Adapter({
        context,
        bridgeBundle,
        siteId: 'site-b',
        clientId: `site-b-${seed}`,
        pageUrl,
        bucket,
        prefix: 'deltas',
        endpoint: s3Config.endpoint,
        region: s3Config.region,
        accessKeyId: s3Config.credentials.accessKeyId,
        secretAccessKey: s3Config.credentials.secretAccessKey,
        forcePathStyle: true,
        nowMs: 2_000,
      });
      const clientC = await createBrowserS3Adapter({
        context,
        bridgeBundle,
        siteId: 'site-c',
        clientId: `site-c-${seed}`,
        pageUrl,
        bucket,
        prefix: 'deltas',
        endpoint: s3Config.endpoint,
        region: s3Config.region,
        accessKeyId: s3Config.credentials.accessKeyId,
        secretAccessKey: s3Config.credentials.secretAccessKey,
        forcePathStyle: true,
        nowMs: 3_000,
      });
      const observer = await createBrowserS3Adapter({
        context,
        bridgeBundle,
        siteId: 'site-observer',
        clientId: `site-observer-${seed}`,
        pageUrl,
        bucket,
        prefix: 'deltas',
        endpoint: s3Config.endpoint,
        region: s3Config.region,
        accessKeyId: s3Config.credentials.accessKeyId,
        secretAccessKey: s3Config.credentials.secretAccessKey,
        forcePathStyle: true,
        nowMs: 3_500,
      });

      try {
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

        const log = new S3ReplicatedLog({
          bucket,
          prefix: 'deltas',
          clientConfig: s3Config,
        });
        expect(await log.getHead('site-a')).toBeGreaterThan(0);
        expect(await log.getHead('site-b')).toBeGreaterThan(0);
        expect(await log.getHead('site-c')).toBeGreaterThan(0);

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

        rawS3Client.destroy();
      } finally {
        await destroyBrowserAdapters([clientA, clientB, clientC, observer]);
      }
    },
    120_000,
  );
});
