import { describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import fc from 'fast-check';
import { buildSelectQuery, parseSql, printSql } from '../../src/core/sql';
import {
  arbGeneratedSelectSpec,
  arbGeneratedSqlCase,
  renderSelectSpec,
  selectSpecToModel,
} from './sql.generators';

describe('SQL parser properties', () => {
  test.prop([arbGeneratedSqlCase])('parses independent SQL-string generator cases', ({ sql, expected }) => {
    expect(parseSql(sql)).toEqual(expected);
  });

  test.prop([arbGeneratedSqlCase])(
    'parse/print/parse is stable over generated SQL strings',
    ({ sql, expected }) => {
      const parsed = parseSql(sql);
      expect(parsed).toEqual(expected);

      const printed = printSql(parsed);
      expect(printed).toBe(sql);
      const reparsed = parseSql(printed);
      expect(reparsed).toEqual(expected);
    },
  );

  test.prop([arbGeneratedSqlCase, fc.constantFrom('', ';', ' ; ', ';   ')])(
    'optional statement terminator is accepted without changing parse result',
    ({ sql, expected }, suffix) => {
      expect(parseSql(`${sql}${suffix}`)).toEqual(expected);
    },
  );
});

describe('SQL query-builder properties', () => {
  test.prop([arbGeneratedSelectSpec])(
    'interface-generated SELECT query matches independent renderer and parser',
    (spec) => {
      const generated = buildSelectQuery(spec);
      const expectedSql = renderSelectSpec(spec);
      expect(generated).toBe(expectedSql);
      expect(parseSql(generated)).toEqual(selectSpecToModel(spec));
    },
  );
});
