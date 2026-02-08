import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { arbOrSetState } from './arbitraries';
import { hasConflictingOrSetEvents, mergeOrSet } from '../../src/core/crdt/orSet';

function tagKey(tag: { addHlc: { wallMs: number; counter: number }; addSite: string }): string {
  return `${tag.addHlc.wallMs}:${tag.addHlc.counter}:${tag.addSite}`;
}

describe('OR-Set properties', () => {
  test.prop([arbOrSetState(), arbOrSetState()])('merge is commutative', (a, b) => {
    fc.pre(!hasConflictingOrSetEvents(a, b));
    expect(mergeOrSet(a, b)).toEqual(mergeOrSet(b, a));
  });

  test.prop([arbOrSetState(), arbOrSetState(), arbOrSetState()])(
    'merge is associative',
    (a, b, c) => {
      fc.pre(
        !hasConflictingOrSetEvents(a, b) &&
          !hasConflictingOrSetEvents(b, c) &&
          !hasConflictingOrSetEvents(a, c),
      );
      expect(mergeOrSet(mergeOrSet(a, b), c)).toEqual(mergeOrSet(a, mergeOrSet(b, c)));
    },
  );

  test.prop([arbOrSetState()])('merge is idempotent', (a) => {
    expect(mergeOrSet(a, a)).toEqual(a);
  });

  test.prop([arbOrSetState(), arbOrSetState()])(
    'merged elements never contain a tombstoned tag',
    (a, b) => {
      fc.pre(!hasConflictingOrSetEvents(a, b));
      const merged = mergeOrSet(a, b);
      const tombstones = new Set(merged.tombstones.map((tag) => tagKey(tag)));
      expect(merged.elements.every((element) => !tombstones.has(tagKey(element.tag)))).toBe(true);
    },
  );
});
