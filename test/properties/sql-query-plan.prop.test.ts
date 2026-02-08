import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import {
  buildSelectPlan,
  buildSelectPlanFromSql,
  buildSelectQuery,
  parseSql,
} from '../../src/core/sql';
import {
  arbGeneratedSelectPlanCase,
  deriveModelSelectPlan,
  selectSpecToModel,
} from './sql.generators';

describe('SQL query generation properties', () => {
  test.prop([arbGeneratedSelectPlanCase])(
    'SELECT sql generates the expected planner query',
    ({ sql, partitionBy, expectedPlan }) => {
      const actual = buildSelectPlanFromSql(sql, {
        partitionBy: partitionBy ?? null,
      });
      expect(actual).toEqual(expectedPlan);
    },
  );

  test.prop([arbGeneratedSelectPlanCase])(
    'interface-generated SELECT query plans match independent model plan',
    ({ spec, partitionBy }) => {
      const sql = buildSelectQuery(spec);
      const expected = deriveModelSelectPlan(selectSpecToModel(spec), partitionBy);
      expect(buildSelectPlanFromSql(sql, { partitionBy: partitionBy ?? null })).toEqual(expected);
    },
  );

  test.prop([arbGeneratedSelectPlanCase])(
    'plan generation from parsed statement and raw SQL are equivalent',
    ({ sql, partitionBy }) => {
      const parsed = parseSql(sql);
      expect(parsed.kind).toBe('select');
      if (parsed.kind !== 'select') {
        return;
      }
      const fromAst = buildSelectPlan(parsed, { partitionBy: partitionBy ?? null });
      const fromSql = buildSelectPlanFromSql(sql, {
        partitionBy: partitionBy ?? null,
      });
      expect(fromAst).toEqual(fromSql);
    },
  );
});
