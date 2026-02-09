import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import type { EncodedCrdtOp, SqlSchema } from '../../src/core/sql';
import {
  RuntimeRowState,
  applyCrdtOpToRows,
  runSelectPlan,
  runtimeRowsToEval,
} from '../../src/core/sqlEval';

function applyOps(ops: EncodedCrdtOp[]) {
  const rows = new Map<string, RuntimeRowState>();
  for (const op of ops) {
    applyCrdtOpToRows(rows, op);
  }
  return rows;
}

const schema: SqlSchema = {
  tasks: {
    pk: 'id',
    partitionBy: null,
    columns: {
      id: { crdt: 'scalar' },
      points: { crdt: 'pn_counter' },
      tags: { crdt: 'or_set' },
      title: { crdt: 'lww' },
      status: { crdt: 'mv_register' },
    },
  },
};

describe('table CRDT composition properties', () => {
  test.prop([
    fc.oneof(fc.string({ minLength: 1, maxLength: 8 }), fc.integer({ min: 0, max: 1000 })),
    fc.hexaString({ minLength: 8, maxLength: 8 }),
    fc.boolean(),
    fc.nat({ max: 1000 }),
  ])(
    'row_exists and counter operations commute on the same row',
    (key, site, exists, amount) => {
      const rowExists: EncodedCrdtOp = {
        tbl: 'tasks',
        key,
        hlc: '0x10',
        site,
        kind: 'row_exists',
        exists,
      };
      const counter: EncodedCrdtOp = {
        tbl: 'tasks',
        key,
        col: 'points',
        hlc: '0x20',
        site,
        kind: 'cell_counter',
        d: 'inc',
        n: amount,
      };

      const left = applyOps([rowExists, counter]);
      const right = applyOps([counter, rowExists]);
      expect(runtimeRowsToEval(left)).toEqual(runtimeRowsToEval(right));
    },
  );

  test.prop([
    fc.oneof(fc.string({ minLength: 1, maxLength: 8 }), fc.integer({ min: 0, max: 1000 })),
    fc.oneof(fc.string({ minLength: 1, maxLength: 8 }), fc.integer({ min: 0, max: 1000 })),
    fc.hexaString({ minLength: 8, maxLength: 8 }),
    fc.string({ minLength: 1, maxLength: 10 }),
  ])(
    'disjoint-key updates commute at table level',
    (keyA, keyB, site, tagValue) => {
      fc.pre(String(keyA) !== String(keyB));
      const a1: EncodedCrdtOp = {
        tbl: 'tasks',
        key: keyA,
        hlc: '0x11',
        site,
        kind: 'row_exists',
        exists: true,
      };
      const a2: EncodedCrdtOp = {
        tbl: 'tasks',
        key: keyA,
        col: 'points',
        hlc: '0x12',
        site,
        kind: 'cell_counter',
        d: 'inc',
        n: 3,
      };
      const b1: EncodedCrdtOp = {
        tbl: 'tasks',
        key: keyB,
        hlc: '0x13',
        site,
        kind: 'row_exists',
        exists: true,
      };
      const b2: EncodedCrdtOp = {
        tbl: 'tasks',
        key: keyB,
        col: 'tags',
        hlc: '0x14',
        site,
        kind: 'cell_or_set_add',
        val: tagValue,
      };

      const left = applyOps([a1, a2, b1, b2]);
      const right = applyOps([b1, b2, a1, a2]);
      expect(runtimeRowsToEval(left)).toEqual(runtimeRowsToEval(right));
    },
  );

  test.prop([
    fc.oneof(fc.string({ minLength: 1, maxLength: 8 }), fc.integer({ min: 0, max: 1000 })),
    fc.hexaString({ minLength: 8, maxLength: 8 }),
    fc.nat({ max: 1000 }),
  ])(
    'delete marker (row_exists=false) is preserved by non-visibility operators',
    (key, site, amount) => {
      const deleted: EncodedCrdtOp = {
        tbl: 'tasks',
        key,
        hlc: '0x30',
        site,
        kind: 'row_exists',
        exists: false,
      };
      const counter: EncodedCrdtOp = {
        tbl: 'tasks',
        key,
        col: 'points',
        hlc: '0x31',
        site,
        kind: 'cell_counter',
        d: 'inc',
        n: amount,
      };

      const rows = applyOps([deleted, counter]);
      const visible = runSelectPlan(
        {
          table: 'tasks',
          columns: '*',
          partitionBy: null,
          route: { kind: 'single_partition', partition: '_default' },
          filters: [{ column: 'id', op: '=', value: key }],
        },
        schema,
        rows,
      );
      expect(visible).toEqual([]);
    },
  );
});
