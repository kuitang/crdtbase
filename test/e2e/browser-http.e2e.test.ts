import { mkdtemp, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { afterAll, afterEach, beforeAll, describe, expect, it } from 'vitest';
import type { Browser, BrowserContext } from 'playwright-core';
import { FileReplicatedLogServer } from '../../src/backend/fileLogServer';
import { HttpReplicatedLog } from '../../src/platform/node/httpReplicatedLog';
import { assertAckedWritesVisible, loadChaosEnv } from './chaosShared';
import { runThreeClientChaosScenario } from './orchestrator';
import {
  buildBrowserBridgeBundle,
  createBrowserHttpAdapter,
  destroyBrowserAdapters,
  launchPlaywrightBrowser,
} from './playwrightBrowserHarness';

describe('Browser x HTTP chaos end-to-end sync', () => {
  const CHAOS = loadChaosEnv();
  let browser: Browser | null = null;
  let bridgeBundle = '';

  let server: FileReplicatedLogServer | null = null;
  let tempRoot: string | null = null;
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
    if (server) {
      await server.stop();
      server = null;
    }
    if (tempRoot) {
      await rm(tempRoot, { recursive: true, force: true });
      tempRoot = null;
    }
  });

  it.each(CHAOS.seeds)(
    'converges under random delayed concurrent browser activity [seed=%s]',
    async (seed) => {
      if (!browser) {
        throw new Error('browser is not started');
      }

      tempRoot = await mkdtemp(join(tmpdir(), 'crdtbase-browser-http-chaos-'));
      const serverDir = join(tempRoot, 'server');
      server = new FileReplicatedLogServer(serverDir);
      const baseUrl = await server.start();

      context = await browser.newContext();

      const clientA = await createBrowserHttpAdapter({
        context,
        bridgeBundle,
        siteId: 'site-a',
        clientId: `site-a-${seed}`,
        baseUrl,
        nowMs: 1_000,
      });
      const clientB = await createBrowserHttpAdapter({
        context,
        bridgeBundle,
        siteId: 'site-b',
        clientId: `site-b-${seed}`,
        baseUrl,
        nowMs: 2_000,
      });
      const clientC = await createBrowserHttpAdapter({
        context,
        bridgeBundle,
        siteId: 'site-c',
        clientId: `site-c-${seed}`,
        baseUrl,
        nowMs: 3_000,
      });
      const observer = await createBrowserHttpAdapter({
        context,
        bridgeBundle,
        siteId: 'site-observer',
        clientId: `site-observer-${seed}`,
        baseUrl,
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

        const log = new HttpReplicatedLog(baseUrl);
        expect(await log.getHead('site-a')).toBeGreaterThan(0);
        expect(await log.getHead('site-b')).toBeGreaterThan(0);
        expect(await log.getHead('site-c')).toBeGreaterThan(0);
      } finally {
        await destroyBrowserAdapters([clientA, clientB, clientC, observer]);
      }
    },
    120_000,
  );
});
