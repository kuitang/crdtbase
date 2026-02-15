import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import {
  buildClientSqlExecutionPlanFromSql,
  buildSqlExecutionPlanFromSql,
  generateCrdtOpsFromSql,
} from '../../src/core/sql';
import {
  arbGeneratedSqlCase,
  arbGeneratedSelectPlanCase,
  arbGeneratedWriteOpsCase,
} from './sql.generators';

describe('SQL to CRDT op generation', () => {
  test.prop([arbGeneratedWriteOpsCase])(
    'write SQL generates expected CRDT ops',
    ({ sql, schema, site, hlcSequence, removeTags, expectedOps }) => {
      let index = 0;
      const nextHlc = () => {
        if (index >= hlcSequence.length) {
          throw new Error('nextHlc called too many times');
        }
        const value = hlcSequence[index]!;
        index += 1;
        return value;
      };

      const actual = generateCrdtOpsFromSql(sql, {
        schema,
        site,
        nextHlc,
        resolveSetRemoveTags: () => removeTags ?? [],
      });

      expect(actual).toEqual(expectedOps);
      expect(index).toBe(hlcSequence.length);
    },
  );

  test.prop([arbGeneratedWriteOpsCase])(
    'execution planner includes the same generated write ops',
    ({ sql, schema, site, hlcSequence, removeTags, expectedOps }) => {
      let index = 0;
      const plan = buildSqlExecutionPlanFromSql(sql, {
        schema,
        site,
        nextHlc: () => {
          if (index >= hlcSequence.length) {
            throw new Error('nextHlc called too many times');
          }
          const value = hlcSequence[index]!;
          index += 1;
          return value;
        },
        resolveSetRemoveTags: () => removeTags ?? [],
      });

      expect(plan.kind).toBe('write');
      if (plan.kind !== 'write') {
        return;
      }
      expect(plan.ops).toEqual(expectedOps);
      expect(index).toBe(hlcSequence.length);
    },
  );
});

describe('Client SQL planner restrictions', () => {
  test('DROP TABLE is rejected for append-only schema metadata', () => {
    expect(() =>
      buildClientSqlExecutionPlanFromSql('DROP TABLE tasks;', {
        schema: {},
        site: 'site-a',
        nextHlc: () => '0x1',
      }),
    ).toThrow(/append-only/i);
  });

  test('ALTER TABLE ADD COLUMN maps to replicated metadata write ops', () => {
    const create = buildClientSqlExecutionPlanFromSql(
      'CREATE TABLE tasks (id PRIMARY KEY, title LWW<STRING>);',
      {
        schema: {},
        site: 'site-a',
        nextHlc: (() => {
          let n = 1;
          return () => `0x${(n++).toString(16)}`;
        })(),
      },
    );
    expect(create.kind).toBe('write');
    if (create.kind !== 'write') {
      return;
    }
    expect(create.statementKind).toBe('create_table');
    expect(create.ops.length).toBeGreaterThan(0);

    const alter = buildClientSqlExecutionPlanFromSql(
      'ALTER TABLE tasks ADD COLUMN points COUNTER;',
      {
        schema: {
          tasks: {
            pk: 'id',
            partitionBy: null,
            columns: {
              id: { crdt: 'scalar' },
              title: { crdt: 'lww' },
            },
          },
        },
        site: 'site-a',
        nextHlc: (() => {
          let n = 100;
          return () => `0x${(n++).toString(16)}`;
        })(),
      },
    );
    expect(alter.kind).toBe('write');
    if (alter.kind !== 'write') {
      return;
    }
    expect(alter.statementKind).toBe('alter_table_add_column');
    expect(alter.ops.length).toBeGreaterThan(0);
  });
});

describe('SQL execution planner', () => {
  test.prop([arbGeneratedSelectPlanCase])(
    'SELECT SQL produces expected read plan',
    ({ sql, partitionBy, expectedPlan }) => {
      const plan = buildSqlExecutionPlanFromSql(sql, {
        schema: {
          [expectedPlan.table]: {
            pk: 'id',
            partitionBy: partitionBy ?? null,
            columns: {
              id: { crdt: 'scalar' },
            },
          },
        },
      });

      expect(plan).toEqual({
        kind: 'read',
        select: expectedPlan,
      });
    },
  );

  test.prop([arbGeneratedSqlCase])(
    'CREATE TABLE sql maps to a schema plan',
    ({ sql, expected }) => {
      fc.pre(expected.kind === 'create_table');
      const primaryKeys = expected.columns.filter((column) => column.primaryKey);
      if (primaryKeys.length !== 1) {
        expect(() => buildSqlExecutionPlanFromSql(sql)).toThrow();
        return;
      }

      const plan = buildSqlExecutionPlanFromSql(sql);
      expect(plan.kind).toBe('ddl_create_table');
      if (plan.kind !== 'ddl_create_table') {
        return;
      }

      const expectedSchema = {
        pk: primaryKeys[0]!.name,
        partitionBy: expected.partitionBy ?? null,
        columns: Object.fromEntries(
          expected.columns.map((column) => [
            column.name,
            {
              crdt:
                column.type.kind === 'counter'
                  ? 'pn_counter'
                  : column.type.kind === 'set'
                    ? 'or_set'
                    : column.type.kind === 'register'
                      ? 'mv_register'
                      : column.type.kind === 'scalar' && column.name !== primaryKeys[0]!.name
                        ? 'lww'
                        : column.type.kind,
            },
          ]),
        ),
      };

      expect(plan.table).toBe(expected.table);
      expect(plan.schema).toEqual(expectedSchema);
    },
  );

  test.prop([arbGeneratedSqlCase])(
    'read/ddl statements do not directly generate CRDT ops',
    ({ sql, expected }) => {
      fc.pre(
        expected.kind === 'select' ||
          expected.kind === 'create_table' ||
          expected.kind === 'drop_table',
      );
      expect(() =>
        generateCrdtOpsFromSql(sql, {
          schema: {},
          site: 'deadbeef',
          nextHlc: () => '0x1',
        }),
      ).toThrow();
    },
  );
});
