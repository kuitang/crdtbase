import { join } from 'node:path';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { describe, expect } from 'vitest';
import { compareHlc, createHlcClock } from '../../src/core/hlc';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import { decodeHlcHex } from '../../src/core/sqlEval';
import type { E2eSiteId } from './orchestrator';
import { assertAckedWritesVisible, readPositiveIntEnv } from './chaosShared';
import { BackendMatrixKind, startBackendMatrixHarness } from './backendMatrixHarness';
import {
  buildDeterministicTrace,
  createSeededRng,
  replayDeterministicTraceScenario,
  type DeterministicTraceStep,
} from './deterministicChaos';

type RestartPlan = Record<E2eSiteId, Set<number>>;

type BackendRestartOutcome = {
  rows: Awaited<ReturnType<typeof replayDeterministicTraceScenario>>['normalizedRowsBySite']['site-a'];
};

function constantNow(value: number): () => number {
  return () => value;
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function startHarnessWithRetry(params: {
  kind: BackendMatrixKind;
}): Promise<Awaited<ReturnType<typeof startBackendMatrixHarness>>> {
  let lastError: unknown = null;
  for (let attempt = 0; attempt < 3; attempt += 1) {
    try {
      return await startBackendMatrixHarness(params);
    } catch (error) {
      lastError = error;
      await sleep(250 * (attempt + 1));
    }
  }
  throw lastError instanceof Error ? lastError : new Error(String(lastError));
}

function buildRestartPlan(params: {
  seed: number;
  totalSteps: number;
  maxRestartsPerSite: number;
}): RestartPlan {
  const buildFor = (salt: number): Set<number> => {
    const rng = createSeededRng((params.seed ^ salt) >>> 0);
    const budget = Math.max(1, Math.min(params.maxRestartsPerSite, Math.floor(rng() * (params.maxRestartsPerSite + 1))));
    const chosen = new Set<number>();

    const minIndex = 1;
    const maxIndex = Math.max(1, params.totalSteps - 2);
    while (chosen.size < budget) {
      const index = minIndex + Math.floor(rng() * (maxIndex - minIndex + 1));
      chosen.add(index);
    }
    return chosen;
  };

  return {
    'site-a': buildFor(0x9e3779b9),
    'site-b': buildFor(0x85ebca6b),
    'site-c': buildFor(0xc2b2ae35),
  };
}

async function runRestartScenarioOnBackend(params: {
  kind: BackendMatrixKind;
  seed: number;
  trace: DeterministicTraceStep[];
  restartPlan: RestartPlan;
  rowIds: string[];
  drainRounds: number;
  quiescenceRounds: number;
}): Promise<BackendRestartOutcome> {
  const harness = await startHarnessWithRetry({ kind: params.kind });

  try {
    const dataRoot = join(harness.rootDir, 'restart-clients');
    const dataDirs: Record<E2eSiteId, string> = {
      'site-a': join(dataRoot, 'site-a'),
      'site-b': join(dataRoot, 'site-b'),
      'site-c': join(dataRoot, 'site-c'),
    };

    const nowBySite: Record<E2eSiteId, () => number> = {
      'site-a': constantNow(1_000),
      'site-b': constantNow(2_000),
      'site-c': constantNow(3_000),
    };

    const clients = {
      'site-a': await NodeCrdtClient.open({
        siteId: 'site-a',
        log: harness.createLog(),
        dataDir: dataDirs['site-a'],
        clock: createHlcClock({ nowWallMs: nowBySite['site-a'] }),
      }),
      'site-b': await NodeCrdtClient.open({
        siteId: 'site-b',
        log: harness.createLog(),
        dataDir: dataDirs['site-b'],
        clock: createHlcClock({ nowWallMs: nowBySite['site-b'] }),
      }),
      'site-c': await NodeCrdtClient.open({
        siteId: 'site-c',
        log: harness.createLog(),
        dataDir: dataDirs['site-c'],
        clock: createHlcClock({ nowWallMs: nowBySite['site-c'] }),
      }),
    };

    const observer = await NodeCrdtClient.open({
      siteId: 'site-observer',
      log: harness.createLog(),
      dataDir: join(dataRoot, 'site-observer'),
      clock: createHlcClock({ nowWallMs: constantNow(3_500) }),
    });

    const reopen = async (siteId: E2eSiteId): Promise<void> => {
      clients[siteId] = await NodeCrdtClient.open({
        siteId,
        log: harness.createLog(),
        dataDir: dataDirs[siteId],
        clock: createHlcClock({ nowWallMs: nowBySite[siteId] }),
      });
    };

    const result = await replayDeterministicTraceScenario({
      clients,
      observer,
      trace: params.trace,
      config: {
        rowIds: params.rowIds,
        drainRounds: params.drainRounds,
        quiescenceRounds: params.quiescenceRounds,
      },
      afterStep: async ({ stepIndex }) => {
        for (const siteId of Object.keys(params.restartPlan) as E2eSiteId[]) {
          if (params.restartPlan[siteId].has(stepIndex)) {
            await reopen(siteId);
          }
        }
      },
    });

    const rows = result.normalizedRowsBySite['site-a'];
    assertAckedWritesVisible({
      rows,
      expectedPointsByRow: result.expectedPointsByRow,
      expectedTagsByRow: result.expectedTagsByRow,
    });

    const inspector = harness.createLog();
    for (const siteId of ['site-a', 'site-b', 'site-c'] as const) {
      const entries = await inspector.readSince(siteId, 0);
      for (let index = 1; index < entries.length; index += 1) {
        const previous = entries[index - 1]!;
        const next = entries[index]!;
        expect(next.seq).toBe(previous.seq + 1);
        expect(compareHlc(decodeHlcHex(next.hlc), decodeHlcHex(previous.hlc))).toBeGreaterThan(0);
      }
    }

    return { rows };
  } finally {
    await harness.stop();
  }
}

describe.sequential('Crash/restart chaos properties across backends', () => {
  const numRuns = readPositiveIntEnv('E2E_RESTART_NUM_RUNS', 2);
  const timeoutMs = readPositiveIntEnv('E2E_RESTART_TIMEOUT_MS', 300_000);
  const stepsPerClient = readPositiveIntEnv('E2E_RESTART_STEPS', 28);
  const maxDelayMs = readPositiveIntEnv('E2E_RESTART_DELAY_MS', 3);
  const drainRounds = readPositiveIntEnv('E2E_RESTART_DRAIN_ROUNDS', 20);
  const quiescenceRounds = readPositiveIntEnv('E2E_RESTART_QUIESCENCE_ROUNDS', 3);
  const maxRestartsPerSite = readPositiveIntEnv('E2E_RESTART_MAX_PER_SITE', 3);
  const rowIds = ['t1', 't2', 't3', 't4', 't5'];

  test
    .prop([fc.integer()], { numRuns })
    ('random restart points preserve convergence and persisted-HLC monotonicity on all backends', async (rawSeed) => {
      const seed = rawSeed | 0;
      const trace = buildDeterministicTrace({
        seed,
        stepsPerClient,
        maxDelayMs,
        rowIds,
      });
      const restartPlan = buildRestartPlan({
        seed,
        totalSteps: trace.length,
        maxRestartsPerSite,
      });

      const http = await runRestartScenarioOnBackend({
        kind: 'http',
        seed,
        trace,
        restartPlan,
        rowIds,
        drainRounds,
        quiescenceRounds,
      });
      const s3Minio = await runRestartScenarioOnBackend({
        kind: 's3-minio',
        seed,
        trace,
        restartPlan,
        rowIds,
        drainRounds,
        quiescenceRounds,
      });

      // Restart behavior should still converge to backend-independent state.
      expect(http.rows).toEqual(s3Minio.rows);
    }, timeoutMs);
});
