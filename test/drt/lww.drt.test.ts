import { beforeAll, afterAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import { LeanDrtClient } from './harness';
import { arbLwwState } from '../properties/arbitraries';
import { mergeLww } from '../../src/core/crdt/lww';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;

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

  drt.prop([arbLwwState(), arbLwwState()])('merge matches Lean oracle', async (a, b) => {
    const tsResult = mergeLww(a, b);
    const leanResult = await client!.send<{ result: typeof tsResult }>({
      type: 'lww_merge',
      a,
      b,
    });
    expect(tsResult).toEqual(leanResult.result);
  });
});
