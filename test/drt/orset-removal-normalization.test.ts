import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { applyCrdtOpToRows, type SqlEvalOutcome } from '../../src/core/sqlEval';
import type { CellOrSetRemoveOp, SetRemoveTag } from '../../src/core/sql';
import { normalizeResult } from './sql-script-utils';

const arbTags = fc.array(fc.record({
  hlc: fc.integer({ min: 0, max: 65535 }).map((n) => `0x${n.toString(16)}`),
  site: fc.hexaString({ minLength: 8, maxLength: 8 }),
}), { minLength: 1, maxLength: 12 });

function op(tags: SetRemoveTag[]): CellOrSetRemoveOp {
  return { kind: 'cell_or_set_remove', tbl: 'tasks', key: 'task-1', col: 'tags',
    hlc: '0xffff', site: '00000000', tags };
}

function result(tags: SetRemoveTag[]): SqlEvalOutcome['result'] {
  return { kind: 'write', statementKind: 'remove', ops: [op(tags)] };
}

describe('Observed removal events in differential comparisons', () => {
  test.prop([arbTags.chain((tags) => fc.shuffledSubarray(tags, {
    minLength: tags.length, maxLength: tags.length,
  }).map((permutation) => ({ tags, permutation })))])(
    'normalizes only permutations that have identical real CRDT effects',
    ({ tags, permutation }) => {
      const original = new Map();
      const reordered = new Map();
      applyCrdtOpToRows(original, op(tags));
      applyCrdtOpToRows(reordered, op(permutation));
      expect(original).toEqual(reordered);
      expect(normalizeResult(result(tags))).toEqual(normalizeResult(result(permutation)));

      // Neither lost observations nor different identities may be hidden.
      expect(normalizeResult(result(tags))).not.toEqual(normalizeResult(result(tags.slice(1))));
      const first = tags[0]!;
      const changed = { ...first, site: `${first.site[0] === '0' ? '1' : '0'}${first.site.slice(1)}` };
      expect(normalizeResult(result(tags))).not.toEqual(normalizeResult(result([changed, ...tags.slice(1)])));
    },
  );
});
