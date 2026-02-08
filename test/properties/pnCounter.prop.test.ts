import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import { applyPnCounterDelta, mergePnCounter, pnCounterValue } from '../../src/core/crdt/pnCounter';
import { arbPnCounter, arbSiteId } from './arbitraries';
import fc from 'fast-check';

describe('PN-Counter properties', () => {
  test.prop([arbPnCounter(), arbPnCounter()])('merge is commutative', (a, b) => {
    expect(mergePnCounter(a, b)).toEqual(mergePnCounter(b, a));
  });

  test.prop([arbPnCounter(), arbPnCounter(), arbPnCounter()])(
    'merge is associative',
    (a, b, c) => {
      expect(mergePnCounter(mergePnCounter(a, b), c)).toEqual(mergePnCounter(a, mergePnCounter(b, c)));
    },
  );

  test.prop([arbPnCounter()])('merge is idempotent', (a) => {
    expect(mergePnCounter(a, a)).toEqual(a);
  });

  test.prop([arbPnCounter(), arbSiteId(), fc.nat({ max: 1_000_000 })])(
    'applying an increment increases materialized value by amount',
    (state, site, amount) => {
      const next = applyPnCounterDelta(state, site, 'inc', amount);
      expect(pnCounterValue(next)).toBe(pnCounterValue(state) + amount);
    },
  );
});
