import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { LeanDrtClient } from './harness';
import { arbLwwState, arbMvRegister, arbOrSetState, arbPnCounter } from '../properties/arbitraries';
import { isConflictingLwwEvent, mergeLww } from '../../src/core/crdt/lww';
import { hasConflictingMvEvents, mergeMvRegister } from '../../src/core/crdt/mvRegister';
import { hasConflictingOrSetEvents, mergeOrSet } from '../../src/core/crdt/orSet';
import { mergePnCounter, normalizePnCounter, PnCounter } from '../../src/core/crdt/pnCounter';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 25);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 45_000);

type PnWireEntry = {
  site: string;
  n: number;
};

type PnWire = {
  inc: PnWireEntry[];
  dec: PnWireEntry[];
};

function compareKeys(left: string, right: string): number {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function toPnWire(counter: PnCounter): PnWire {
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

function fromPnWire(wire: PnWire): PnCounter {
  const inc: Record<string, number> = {};
  const dec: Record<string, number> = {};
  for (const entry of wire.inc) {
    if (entry.n === 0) {
      continue;
    }
    inc[entry.site] = (inc[entry.site] ?? 0) + entry.n;
  }
  for (const entry of wire.dec) {
    if (entry.n === 0) {
      continue;
    }
    dec[entry.site] = (dec[entry.site] ?? 0) + entry.n;
  }
  return normalizePnCounter({ inc, dec });
}

function hasConflictingLwwList<T>(states: T[], isConflict: (a: T, b: T) => boolean): boolean {
  for (let leftIndex = 0; leftIndex < states.length; leftIndex += 1) {
    for (let rightIndex = leftIndex + 1; rightIndex < states.length; rightIndex += 1) {
      if (isConflict(states[leftIndex]!, states[rightIndex]!)) {
        return true;
      }
    }
  }
  return false;
}

function foldTs<T>(items: T[], mergeFn: (left: T, right: T) => T): T | undefined {
  let acc: T | undefined;
  for (const item of items) {
    acc = acc === undefined ? item : mergeFn(acc, item);
  }
  return acc;
}

async function foldLean<T>(
  items: T[],
  mergeFn: (left: T, right: T) => Promise<T>,
): Promise<T | undefined> {
  let acc: T | undefined;
  for (const item of items) {
    acc = acc === undefined ? item : await mergeFn(acc, item);
  }
  return acc;
}

function applyCompactionSplitTs<T>(
  items: T[],
  splitIndex: number,
  mergeFn: (left: T, right: T) => T,
): T | undefined {
  const prefix = items.slice(0, splitIndex);
  const suffix = items.slice(splitIndex);
  let acc = foldTs(prefix, mergeFn);
  for (const item of suffix) {
    acc = acc === undefined ? item : mergeFn(acc, item);
  }
  return acc;
}

async function applyCompactionSplitLean<T>(
  items: T[],
  splitIndex: number,
  mergeFn: (left: T, right: T) => Promise<T>,
): Promise<T | undefined> {
  const prefix = items.slice(0, splitIndex);
  const suffix = items.slice(splitIndex);
  let acc = await foldLean(prefix, mergeFn);
  for (const item of suffix) {
    acc = acc === undefined ? item : await mergeFn(acc, item);
  }
  return acc;
}

function splitPoints(length: number): number[] {
  return Array.from({ length: length + 1 }, (_, index) => index);
}

describe('DRT: Compaction split law', () => {
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
    .prop([fc.array(arbLwwState(), { maxLength: 12 })], { numRuns: drtRuns })
    ('LWW: every prefix/suffix split matches direct fold and Lean', async (states) => {
      fc.pre(!hasConflictingLwwList(states, isConflictingLwwEvent));

      const mergeLean = async (left: (typeof states)[number], right: (typeof states)[number]) => {
        const response = await client!.send<{ result: (typeof states)[number] }>({
          type: 'lww_merge',
          a: left,
          b: right,
        });
        return response.result;
      };

      const directTs = foldTs(states, mergeLww);
      const directLean = await foldLean(states, mergeLean);
      expect(directTs).toEqual(directLean);

      for (const splitIndex of splitPoints(states.length)) {
        const splitTs = applyCompactionSplitTs(states, splitIndex, mergeLww);
        const splitLean = await applyCompactionSplitLean(states, splitIndex, mergeLean);
        expect(splitTs).toEqual(directTs);
        expect(splitLean).toEqual(directLean);
      }
    }, drtTimeoutMs);

  drt
    .prop([fc.array(arbPnCounter(), { maxLength: 12 })], { numRuns: drtRuns })
    ('PN-Counter: every prefix/suffix split matches direct fold and Lean', async (states) => {
      const mergeLean = async (left: PnCounter, right: PnCounter) => {
        const response = await client!.send<{ result: PnWire }>({
          type: 'pn_merge',
          a: toPnWire(left),
          b: toPnWire(right),
        });
        return fromPnWire(response.result);
      };

      const directTs = foldTs(states, mergePnCounter);
      const directLean = await foldLean(states, mergeLean);
      expect(directTs).toEqual(directLean);

      for (const splitIndex of splitPoints(states.length)) {
        const splitTs = applyCompactionSplitTs(states, splitIndex, mergePnCounter);
        const splitLean = await applyCompactionSplitLean(states, splitIndex, mergeLean);
        expect(splitTs).toEqual(directTs);
        expect(splitLean).toEqual(directLean);
      }
    }, drtTimeoutMs);

  drt
    .prop([fc.array(arbOrSetState(), { maxLength: 12 })], { numRuns: drtRuns })
    ('OR-Set: every prefix/suffix split matches direct fold and Lean', async (states) => {
      fc.pre(!hasConflictingLwwList(states, hasConflictingOrSetEvents));

      const mergeLean = async (
        left: (typeof states)[number],
        right: (typeof states)[number],
      ) => {
        const response = await client!.send<{ result: (typeof states)[number] }>({
          type: 'or_set_merge',
          a: left,
          b: right,
        });
        return response.result;
      };

      const directTs = foldTs(states, mergeOrSet);
      const directLean = await foldLean(states, mergeLean);
      expect(directTs).toEqual(directLean);

      for (const splitIndex of splitPoints(states.length)) {
        const splitTs = applyCompactionSplitTs(states, splitIndex, mergeOrSet);
        const splitLean = await applyCompactionSplitLean(states, splitIndex, mergeLean);
        expect(splitTs).toEqual(directTs);
        expect(splitLean).toEqual(directLean);
      }
    }, drtTimeoutMs);

  drt
    .prop([fc.array(arbMvRegister(), { maxLength: 12 })], { numRuns: drtRuns })
    ('MV-Register: every prefix/suffix split matches direct fold and Lean', async (states) => {
      fc.pre(!hasConflictingLwwList(states, hasConflictingMvEvents));

      const mergeLean = async (
        left: (typeof states)[number],
        right: (typeof states)[number],
      ) => {
        const response = await client!.send<{ result: (typeof states)[number] }>({
          type: 'mv_merge',
          a: left,
          b: right,
        });
        return response.result;
      };

      const directTs = foldTs(states, mergeMvRegister);
      const directLean = await foldLean(states, mergeLean);
      expect(directTs).toEqual(directLean);

      for (const splitIndex of splitPoints(states.length)) {
        const splitTs = applyCompactionSplitTs(states, splitIndex, mergeMvRegister);
        const splitLean = await applyCompactionSplitLean(states, splitIndex, mergeLean);
        expect(splitTs).toEqual(directTs);
        expect(splitLean).toEqual(directLean);
      }
    }, drtTimeoutMs);
});
