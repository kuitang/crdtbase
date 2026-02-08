import { beforeAll, afterAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import { LeanDrtClient } from './harness';
import { arbPnCounter } from '../properties/arbitraries';
import { mergePnCounter, PnCounter } from '../../src/core/crdt/pnCounter';

type PnWireEntry = {
  site: string;
  n: number;
};

type PnWire = {
  inc: PnWireEntry[];
  dec: PnWireEntry[];
};

function toWire(counter: PnCounter): PnWire {
  const compareKeys = (left: string, right: string): number => {
    if (left < right) return -1;
    if (left > right) return 1;
    return 0;
  };
  const encode = (entries: Record<string, number>): PnWireEntry[] =>
    Object.entries(entries)
      .filter(([, n]) => n !== 0)
      .sort(([left], [right]) => compareKeys(left, right))
      .map(([site, n]) => ({ site, n }));
  return {
    inc: encode(counter.inc),
    dec: encode(counter.dec),
  };
}

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

describe('DRT: PN-Counter', () => {
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
    .prop([arbPnCounter(), arbPnCounter()], { numRuns: drtRuns })
    ('merge matches Lean oracle', async (a, b) => {
      const tsResult = mergePnCounter(a, b);
      const leanResult = await client!.send<{ result: PnWire }>({
        type: 'pn_merge',
        a: toWire(a),
        b: toWire(b),
      });
      expect(toWire(tsResult)).toEqual(leanResult.result);
    }, drtTimeoutMs);
});
