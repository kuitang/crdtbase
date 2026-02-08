import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { arbMvRegister } from './arbitraries';
import {
  hasConflictingMvEvents,
  mergeMvRegister,
} from '../../src/core/crdt/mvRegister';

function eventKey(value: {
  hlc: { wallMs: number; counter: number };
  site: string;
}): string {
  return `${value.hlc.wallMs}:${value.hlc.counter}:${value.site}`;
}

describe('MV-Register properties', () => {
  test.prop([arbMvRegister(), arbMvRegister()])('merge is commutative', (a, b) => {
    fc.pre(!hasConflictingMvEvents(a, b));
    expect(mergeMvRegister(a, b)).toEqual(mergeMvRegister(b, a));
  });

  test.prop([arbMvRegister(), arbMvRegister(), arbMvRegister()])(
    'merge is associative',
    (a, b, c) => {
      fc.pre(
        !hasConflictingMvEvents(a, b) &&
          !hasConflictingMvEvents(b, c) &&
          !hasConflictingMvEvents(a, c),
      );
      expect(mergeMvRegister(mergeMvRegister(a, b), c)).toEqual(mergeMvRegister(a, mergeMvRegister(b, c)));
    },
  );

  test.prop([arbMvRegister()])('merge is idempotent', (a) => {
    expect(mergeMvRegister(a, a)).toEqual(a);
  });

  test.prop([arbMvRegister(), arbMvRegister()])(
    'merged values keep unique (hlc, site) event identities',
    (a, b) => {
      fc.pre(!hasConflictingMvEvents(a, b));
      const merged = mergeMvRegister(a, b);
      const keys = merged.values.map((value) => eventKey(value));
      expect(new Set(keys).size).toBe(keys.length);
    },
  );
});
