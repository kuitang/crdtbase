import { beforeAll, afterAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import { arbOrSetState } from '../properties/arbitraries';
import { hasConflictingOrSetEvents, mergeOrSet } from '../../src/core/crdt/orSet';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

describe('DRT: OR-Set', () => {
  let client: LeanDrtClient | null = null;

  beforeAll(() => {
    if (leanBin) {
      client = new LeanDrtClient(leanBin);
    }
  });

  afterAll(() => {
    client?.close();
  });

  drt
    .prop([arbOrSetState(), arbOrSetState()], { numRuns: drtRuns })
    ('merge matches Lean oracle', async (a, b) => {
      fc.pre(!hasConflictingOrSetEvents(a, b));
      const tsResult = mergeOrSet(a, b);
      const leanResult = await client!.send<{ result: typeof tsResult }>({
        type: 'or_set_merge',
        a,
        b,
      });
      expect(tsResult).toEqual(leanResult.result);
    }, drtTimeoutMs);
});
