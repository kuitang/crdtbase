import { join } from 'node:path';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { describe, expect } from 'vitest';
import { createHlcClock } from '../../src/core/hlc';
import { NodeCrdtClient } from '../../src/platform/node/nodeClient';
import type { E2eSiteId } from './orchestrator';
import { assertAckedWritesVisible, readPositiveIntEnv } from './chaosShared';
import { BackendMatrixKind, startBackendMatrixHarness } from './backendMatrixHarness';
import {
  buildDeterministicTrace,
  replayDeterministicTraceScenario,
  type DeterministicTraceStep,
} from './deterministicChaos';

type BackendOutcome = {
  rows: Awaited<ReturnType<typeof replayDeterministicTraceScenario>>['normalizedRowsBySite']['site-a'];
  heads: Record<E2eSiteId, number>;
};

function deterministicNow(start: number): () => number {
  let tick = start;
  return () => {
    tick += 1;
    return tick;
  };
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

async function runTraceOnBackend(params: {
  kind: BackendMatrixKind;
  seed: number;
  trace: DeterministicTraceStep[];
  rowIds: string[];
  drainRounds: number;
  quiescenceRounds: number;
}): Promise<BackendOutcome> {
  const harness = await startHarnessWithRetry({ kind: params.kind });

  try {
    const dataRoot = join(harness.rootDir, 'clients');
    const clocks: Record<string, () => number> = {
      'site-a': deterministicNow(1_000),
      'site-b': deterministicNow(2_000),
      'site-c': deterministicNow(3_000),
      'site-observer': deterministicNow(3_500),
    };

    const clientA = await NodeCrdtClient.open({
      siteId: 'site-a',
      log: harness.createLog(),
      dataDir: join(dataRoot, 'site-a'),
      clock: createHlcClock({ nowWallMs: clocks['site-a'] }),
    });
    const clientB = await NodeCrdtClient.open({
      siteId: 'site-b',
      log: harness.createLog(),
      dataDir: join(dataRoot, 'site-b'),
      clock: createHlcClock({ nowWallMs: clocks['site-b'] }),
    });
    const clientC = await NodeCrdtClient.open({
      siteId: 'site-c',
      log: harness.createLog(),
      dataDir: join(dataRoot, 'site-c'),
      clock: createHlcClock({ nowWallMs: clocks['site-c'] }),
    });
    const observer = await NodeCrdtClient.open({
      siteId: 'site-observer',
      log: harness.createLog(),
      dataDir: join(dataRoot, 'site-observer'),
      clock: createHlcClock({ nowWallMs: clocks['site-observer'] }),
    });

    const result = await replayDeterministicTraceScenario({
      clients: {
        'site-a': clientA,
        'site-b': clientB,
        'site-c': clientC,
      },
      observer,
      trace: params.trace,
      config: {
        rowIds: params.rowIds,
        drainRounds: params.drainRounds,
        quiescenceRounds: params.quiescenceRounds,
      },
    });

    const rows = result.normalizedRowsBySite['site-a'];
    assertAckedWritesVisible({
      rows,
      expectedPointsByRow: result.expectedPointsByRow,
      expectedTagsByRow: result.expectedTagsByRow,
    });

    const inspector = harness.createLog();
    const heads: Record<E2eSiteId, number> = {
      'site-a': await inspector.getHead('site-a'),
      'site-b': await inspector.getHead('site-b'),
      'site-c': await inspector.getHead('site-c'),
    };

    return { rows, heads };
  } finally {
    await harness.stop();
  }
}

describe.sequential('Cross-backend deterministic parity properties', () => {
  const numRuns = readPositiveIntEnv('E2E_PARITY_NUM_RUNS', 2);
  const timeoutMs = readPositiveIntEnv('E2E_PARITY_TIMEOUT_MS', 240_000);
  const stepsPerClient = readPositiveIntEnv('E2E_PARITY_STEPS', 30);
  const maxDelayMs = readPositiveIntEnv('E2E_PARITY_DELAY_MS', 4);
  const drainRounds = readPositiveIntEnv('E2E_PARITY_DRAIN_ROUNDS', 20);
  const quiescenceRounds = readPositiveIntEnv('E2E_PARITY_QUIESCENCE_ROUNDS', 3);
  const rowIds = ['t1', 't2', 't3', 't4', 't5'];

  test
    .prop([fc.integer()], { numRuns })
    ('replays identical precomputed traces and converges to identical rows/heads across backends', async (rawSeed) => {
      const seed = rawSeed | 0;
      const trace = buildDeterministicTrace({
        seed,
        stepsPerClient,
        maxDelayMs,
        rowIds,
      });

      const http = await runTraceOnBackend({
        kind: 'http',
        seed,
        trace,
        rowIds,
        drainRounds,
        quiescenceRounds,
      });
      const s3Minio = await runTraceOnBackend({
        kind: 's3-minio',
        seed,
        trace,
        rowIds,
        drainRounds,
        quiescenceRounds,
      });

      expect(http.rows).toEqual(s3Minio.rows);
      expect(http.heads).toEqual(s3Minio.heads);
    }, timeoutMs);
});
