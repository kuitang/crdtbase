import fc from 'fast-check';
import { HLC_LIMITS, Hlc } from '../../src/core/hlc';
import { LwwRegister } from '../../src/core/crdt/lww';

export const arbHlc = (): fc.Arbitrary<Hlc> =>
  fc.record({
    wallMs: fc.nat({ max: HLC_LIMITS.wallMsMax - 1 }),
    counter: fc.nat({ max: HLC_LIMITS.counterMax - 1 }),
  });

export const arbSiteId = (): fc.Arbitrary<string> =>
  fc.hexaString({ minLength: 8, maxLength: 8 });

export const arbScalar = (): fc.Arbitrary<string | number | boolean | null> =>
  fc.oneof(
    fc.string({ maxLength: 40 }),
    fc.integer({ min: -1_000_000, max: 1_000_000 }),
    fc.boolean(),
    fc.constant(null),
  );

export const arbLwwState = (): fc.Arbitrary<LwwRegister<string | number | boolean | null>> =>
  fc.record({
    val: arbScalar(),
    hlc: arbHlc(),
    site: arbSiteId(),
  });
