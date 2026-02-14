import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import {
  HLC_DRIFT_LIMIT_MS,
  HLC_LIMITS,
  PersistedHlcFence,
  assertHlcDrift,
  assertHlcStrictlyIncreases,
  createMonotonicWallClock,
  nextMonotonicHlc,
  recvMonotonicHlc,
} from '../../src/core/hlc';
import { mergeLww } from '../../src/core/crdt/lww';
import { LwwConflictGuard } from '../../src/core/crdt/lwwConflictGuard';
import { applyPnCounterDelta } from '../../src/core/crdt/pnCounter';
import { mergeOrSet } from '../../src/core/crdt/orSet';
import { mergeMvRegister } from '../../src/core/crdt/mvRegister';
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

describe('HLC runtime clock assumptions', () => {
  test.prop([
    fc.record({
      wallMs: fc.integer({ min: 0, max: HLC_LIMITS.wallMsMax - 1 }),
      counter: fc.integer({ min: 0, max: HLC_LIMITS.counterMax - 1 }),
    }),
  ])('drift assertion accepts in-range clocks', (hlc) => {
    const now = hlc.wallMs + HLC_DRIFT_LIMIT_MS;
    expect(() => assertHlcDrift(hlc, now)).not.toThrow();
  });

  test.prop([
    fc.record({
      wallMs: fc.integer({ min: 0, max: HLC_LIMITS.wallMsMax - 1 }),
      counter: fc.integer({ min: 0, max: HLC_LIMITS.counterMax - 1 }),
    }),
  ])('drift assertion rejects clocks beyond limit', (hlc) => {
    const now = hlc.wallMs >= HLC_DRIFT_LIMIT_MS + 1 ? hlc.wallMs - (HLC_DRIFT_LIMIT_MS + 1) : 0;
    fc.pre(hlc.wallMs > now + HLC_DRIFT_LIMIT_MS);
    expect(() => assertHlcDrift(hlc, now)).toThrow(/drift/i);
  });

  test.prop([
    fc.record({
      wallMs: fc.integer({ min: HLC_DRIFT_LIMIT_MS + 1, max: HLC_LIMITS.wallMsMax - 1 }),
      counter: fc.integer({ min: 0, max: HLC_LIMITS.counterMax - 1 }),
    }),
  ])('nextMonotonicHlc rejects persisted high-water mark beyond drift limit', (previous) => {
    const now = previous.wallMs - (HLC_DRIFT_LIMIT_MS + 1);
    expect(() => nextMonotonicHlc(previous, now)).toThrow(/drift/i);
  });

  test.prop([
    fc.record({
      wallMs: fc.integer({ min: HLC_DRIFT_LIMIT_MS + 1, max: HLC_LIMITS.wallMsMax - 1 }),
      counter: fc.integer({ min: 0, max: HLC_LIMITS.counterMax - 2 }),
    }),
  ])('recvMonotonicHlc rejects remote clock beyond drift limit', (remote) => {
    const now = remote.wallMs - (HLC_DRIFT_LIMIT_MS + 1);
    expect(() => recvMonotonicHlc(null, remote, now)).toThrow(/drift/i);
  });

  test.prop([
    fc.record({
      wallMs: fc.integer({ min: 0, max: HLC_LIMITS.wallMsMax - 2 }),
      counter: fc.integer({ min: 0, max: HLC_LIMITS.counterMax - 2 }),
    }),
  ])('recvMonotonicHlc yields value strictly greater than remote when remote dominates wall time', (remote) => {
    const now = remote.wallMs === 0 ? 0 : remote.wallMs - 1;
    const received = recvMonotonicHlc(null, remote, now);
    expect(received.wallMs).toBe(remote.wallMs);
    expect(received.counter).toBe(remote.counter + 1);
  });

  test.prop([fc.array(fc.integer({ min: 0, max: 10_000 }), { minLength: 4, maxLength: 20 })])(
    'monotonic wall clock wrapper never moves backward',
    (wallSamples) => {
      let index = 0;
      const dateNow = () => wallSamples[Math.min(index++, wallSamples.length - 1)]!;
      const monotonicWall = createMonotonicWallClock({
        dateNow,
        performance: null,
      });
      let previous = -1;
      for (let i = 0; i < wallSamples.length; i += 1) {
        const current = monotonicWall();
        expect(current).toBeGreaterThanOrEqual(previous);
        previous = current;
      }
    },
  );
});

describe('PN-Counter invariant enforcement', () => {
  test.prop([
    arbSiteId(),
    fc.oneof(
      fc.integer({ min: -1_000_000, max: -1 }),
      fc.constant(Number.NaN),
      fc.constant(Number.POSITIVE_INFINITY),
      fc.constant(Number.NEGATIVE_INFINITY),
    ),
  ])('counter delta rejects invalid amounts', (site, amount) => {
    const initial = { inc: {}, dec: {} };
    expect(() => applyPnCounterDelta(initial, site, 'inc', amount)).toThrow(
      /finite non-negative/,
    );
  });
});

describe('OR-Set invariant enforcement', () => {
  test.prop([arbHlc(), arbSiteId(), fc.tuple(arbScalar(), arbScalar())])(
    'merge rejects conflicting payloads for same add-tag',
    (hlc, site, [leftVal, rightVal]) => {
      fc.pre(!Object.is(leftVal, rightVal));
      const a = {
        elements: [{ val: leftVal, tag: { addHlc: hlc, addSite: site } }],
        tombstones: [],
      };
      const b = {
        elements: [{ val: rightVal, tag: { addHlc: hlc, addSite: site } }],
        tombstones: [],
      };
      expect(() => mergeOrSet(a, b)).toThrow(/conflicting OR-Set add tag identity/);
    },
  );
});

describe('MV-Register invariant enforcement', () => {
  test.prop([arbHlc(), arbSiteId(), fc.tuple(arbScalar(), arbScalar())])(
    'merge rejects conflicting payloads for same (hlc, site)',
    (hlc, site, [leftVal, rightVal]) => {
      fc.pre(!Object.is(leftVal, rightVal));
      const a = {
        values: [{ val: leftVal, hlc, site }],
      };
      const b = {
        values: [{ val: rightVal, hlc, site }],
      };
      expect(() => mergeMvRegister(a, b)).toThrow(/conflicting MV-Register event identity/);
    },
  );
});
