import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { HLC_LIMITS, PersistedHlcFence, assertHlcStrictlyIncreases } from '../../src/core/hlc';
import { mergeLww } from '../../src/core/crdt/lww';
import { LwwConflictGuard } from '../../src/core/crdt/lwwConflictGuard';
import { arbHlc, arbScalar, arbSiteId } from './arbitraries';

describe('LWW invariant enforcement', () => {
  test.prop([arbHlc(), arbSiteId(), fc.tuple(arbScalar(), arbScalar())])(
    'merge rejects conflicting payloads for same (hlc, site)',
    (hlc, site, [leftVal, rightVal]) => {
      fc.pre(!Object.is(leftVal, rightVal));
      const a = { val: leftVal, hlc, site };
      const b = { val: rightVal, hlc, site };
      expect(() => mergeLww(a, b)).toThrow(/conflicting LWW event identity/);
    },
  );

  test.prop([arbHlc(), arbSiteId(), arbScalar()])(
    'merge accepts idempotent replay for same (hlc, site, payload)',
    (hlc, site, val) => {
      const a = { val, hlc, site };
      const b = { val, hlc, site };
      expect(mergeLww(a, b)).toEqual(a);
      expect(mergeLww(b, a)).toEqual(b);
    },
  );

  test.prop([
    fc.string({ minLength: 1, maxLength: 20 }),
    fc.oneof(fc.string({ maxLength: 20 }), fc.integer()),
    fc.string({ minLength: 1, maxLength: 20 }),
    arbSiteId(),
    arbHlc(),
    fc.tuple(arbScalar(), arbScalar()),
  ])(
    'event conflict guard rejects divergent payloads for same identity',
    (table, key, col, site, hlc, [leftVal, rightVal]) => {
      fc.pre(!Object.is(leftVal, rightVal));
      const guard = new LwwConflictGuard();
      const identity = { table, key, col, site, hlc };
      guard.observe(identity, leftVal);
      expect(() => guard.observe(identity, rightVal)).toThrow(/conflicting LWW payload/);
    },
  );
});

describe('HLC monotonic fence', () => {
  test.prop([arbHlc()])('strict monotonic check rejects equal candidate', (hlc) => {
    expect(() => assertHlcStrictlyIncreases(hlc, hlc)).toThrow(/monotonicity violation/);
  });

  test.prop([
    fc.record({
      wallMs: fc.nat({ max: HLC_LIMITS.wallMsMax - 1 }),
      counter: fc.nat({ max: HLC_LIMITS.counterMax - 2 }),
    }),
  ])('strict monotonic check accepts next counter at same wall clock', (previous) => {
    const candidate = { wallMs: previous.wallMs, counter: previous.counter + 1 };
    expect(() => assertHlcStrictlyIncreases(previous, candidate)).not.toThrow();
  });

  test.prop([
    fc.record({
      wallMs: fc.integer({ min: 0, max: HLC_LIMITS.wallMsMax - 2 }),
      counter: fc.integer({ min: 0, max: HLC_LIMITS.counterMax - 2 }),
    }),
  ])('persisted fence blocks rollback writes', (base) => {
    const initial = { wallMs: base.wallMs, counter: base.counter };
    const next = { wallMs: base.wallMs, counter: base.counter + 1 };

    const fence = new PersistedHlcFence(initial);
    expect(() => fence.commit(next)).not.toThrow();
    fence.loadPersisted(next);
    expect(() => fence.commit(next)).toThrow(/monotonicity violation/);
    expect(() => fence.commit(initial)).toThrow(/monotonicity violation/);
  });
});
