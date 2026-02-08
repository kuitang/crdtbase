import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { isConflictingLwwEvent, mergeLww } from '../../src/core/crdt/lww';
import { arbLwwState } from './arbitraries';

describe('LWW properties', () => {
  test.prop([arbLwwState(), arbLwwState()])('merge is commutative', (a, b) => {
    fc.pre(!isConflictingLwwEvent(a, b));
    expect(mergeLww(a, b)).toEqual(mergeLww(b, a));
  });

  test.prop([arbLwwState(), arbLwwState(), arbLwwState()])(
    'merge is associative',
    (a, b, c) => {
      fc.pre(
        !isConflictingLwwEvent(a, b) &&
          !isConflictingLwwEvent(b, c) &&
          !isConflictingLwwEvent(a, c),
      );
      expect(mergeLww(mergeLww(a, b), c)).toEqual(mergeLww(a, mergeLww(b, c)));
    },
  );

  test.prop([arbLwwState()])('merge is idempotent', (a) => {
    expect(mergeLww(a, a)).toEqual(a);
  });
});
