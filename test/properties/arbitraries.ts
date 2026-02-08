import fc from 'fast-check';
import { HLC_LIMITS, Hlc } from '../../src/core/hlc';
import { LwwRegister } from '../../src/core/crdt/lww';
import { normalizePnCounter, PnCounter } from '../../src/core/crdt/pnCounter';
import { canonicalizeOrSet, OrSet, OrSetElement, OrSetTag } from '../../src/core/crdt/orSet';
import {
  canonicalizeMvRegister,
  MvRegister,
  MvRegisterValue,
} from '../../src/core/crdt/mvRegister';

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

const tagKey = (tag: OrSetTag): string =>
  `${tag.addHlc.wallMs}:${tag.addHlc.counter}:${tag.addSite}`;

const mvEventKey = (value: MvRegisterValue<string | number | boolean | null>): string =>
  `${value.hlc.wallMs}:${value.hlc.counter}:${value.site}`;

export const arbPnCounter = (): fc.Arbitrary<PnCounter> =>
  fc
    .record({
      inc: fc.dictionary(arbSiteId(), fc.nat({ max: 1_000_000 })),
      dec: fc.dictionary(arbSiteId(), fc.nat({ max: 1_000_000 })),
    })
    .map(normalizePnCounter);

export const arbOrSetTag = (): fc.Arbitrary<OrSetTag> =>
  fc.record({
    addHlc: arbHlc(),
    addSite: arbSiteId(),
  });

export const arbOrSetElement = (): fc.Arbitrary<OrSetElement<string | number | boolean | null>> =>
  fc.record({
    val: arbScalar(),
    tag: arbOrSetTag(),
  });

export const arbOrSetState = (): fc.Arbitrary<OrSet<string | number | boolean | null>> =>
  fc
    .record({
      elements: fc.uniqueArray(arbOrSetElement(), {
        maxLength: 40,
        selector: (element) => tagKey(element.tag),
      }),
      tombstones: fc.uniqueArray(arbOrSetTag(), {
        maxLength: 40,
        selector: tagKey,
      }),
    })
    .map(canonicalizeOrSet);

export const arbMvValue = (): fc.Arbitrary<MvRegisterValue<string | number | boolean | null>> =>
  fc.record({
    val: arbScalar(),
    hlc: arbHlc(),
    site: arbSiteId(),
  });

export const arbMvRegister =
  (): fc.Arbitrary<MvRegister<string | number | boolean | null>> =>
    fc
      .record({
        values: fc.uniqueArray(arbMvValue(), {
          maxLength: 40,
          selector: mvEventKey,
        }),
      })
      .map(canonicalizeMvRegister);
