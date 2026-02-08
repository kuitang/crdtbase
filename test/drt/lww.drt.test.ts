import { beforeAll, afterAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import { arbLwwState } from '../properties/arbitraries';
import { isConflictingLwwEvent, mergeLww } from '../../src/core/crdt/lww';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

describe('DRT: LWW', () => {
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
    .prop([arbLwwState(), arbLwwState()], { numRuns: drtRuns })
    ('merge matches Lean oracle', async (a, b) => {
      fc.pre(!isConflictingLwwEvent(a, b));
      const tsResult = mergeLww(a, b);
      const leanResult = await client!.send<{ result: typeof tsResult }>({
        type: 'lww_merge',
        a,
        b,
      });
      expect(tsResult).toEqual(leanResult.result);
    }, drtTimeoutMs);
});
