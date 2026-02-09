import { afterAll, beforeAll, describe, expect } from 'vitest';
import { test } from '@fast-check/vitest';
import { LeanDrtClient } from './harness';
import {
  parseSql,
  type SqlSchema,
  type SqlTableSchema,
} from '../../src/core/sql';
import {
  evaluateSqlAst,
  rowStorageKey,
  type SqlEvalColumnState,
  type SqlEvalOutcome,
  type SqlEvalRowState,
  type SqlEvalState,
} from '../../src/core/sqlEval';
import { arbSqlEvalCase } from '../properties/sql-eval.generators';

const leanBin = LeanDrtClient.findBinary();
const drt = leanBin ? test : test.skip;
const drtRuns = Number(process.env.DRT_NUM_RUNS ?? 50);
const drtSeed = process.env.DRT_SEED === undefined ? undefined : Number(process.env.DRT_SEED);
const drtTimeoutMs = Number(process.env.DRT_TIMEOUT_MS ?? 30_000);

type LeanSchema = Array<{
  table: string;
  pk: string;
  partitionBy: string | null;
  columns: Array<{ name: string; crdt: string }>;
}>;

type LeanEvalState = {
  rows: Array<{
    table: string;
    key: string | number;
    columns: Array<{
      column: string;
      state:
        | { typ: 1; val: unknown; hlc: string; site: string }
        | { typ: 2; inc: Array<{ site: string; n: number }>; dec: Array<{ site: string; n: number }> }
        | {
            typ: 3;
            elements: Array<{ val: unknown; hlc: string; site: string }>;
            tombstones: Array<{ hlc: string; site: string }>;
          }
        | {
            typ: 4;
            values: Array<{ val: unknown; hlc: string; site: string }>;
          };
    }>;
  }>;
};

type LeanEvalOutcome = {
  result: SqlEvalOutcome['result'];
  nextState: {
    schema: LeanSchema;
    rows: LeanEvalState['rows'];
  };
};

function sortObjectKeys<T extends Record<string, unknown>>(value: T): T {
  return Object.fromEntries(
    Object.entries(value).sort(([left], [right]) => (left < right ? -1 : left > right ? 1 : 0)),
  ) as T;
}

function normalizeJsonObject(value: unknown): unknown {
  if (Array.isArray(value)) {
    return value.map((entry) => normalizeJsonObject(entry));
  }
  if (value !== null && typeof value === 'object') {
    return Object.fromEntries(
      Object.entries(value as Record<string, unknown>)
        .sort(([left], [right]) => (left < right ? -1 : left > right ? 1 : 0))
        .map(([key, nested]) => [key, normalizeJsonObject(nested)]),
    );
  }
  return value;
}

function normalizeReadCell(value: unknown): unknown {
  if (!Array.isArray(value)) {
    return normalizeJsonObject(value);
  }
  return value
    .map((entry) => normalizeJsonObject(entry))
    .sort((left, right) => {
      const leftKey = JSON.stringify(left);
      const rightKey = JSON.stringify(right);
      if (leftKey < rightKey) return -1;
      if (leftKey > rightKey) return 1;
      return 0;
    });
}

function normalizeColumnState(state: SqlEvalColumnState): SqlEvalColumnState {
  switch (state.typ) {
    case 1:
      return state;
    case 2:
      return {
        typ: 2,
        inc: sortObjectKeys(state.inc),
        dec: sortObjectKeys(state.dec),
      };
    case 3:
      return {
        typ: 3,
        elements: [...state.elements].sort((a, b) => {
          const left = `${a.hlc}:${a.site}:${JSON.stringify(a.val)}`;
          const right = `${b.hlc}:${b.site}:${JSON.stringify(b.val)}`;
          if (left < right) return -1;
          if (left > right) return 1;
          return 0;
        }),
        tombstones: [...state.tombstones].sort((a, b) => {
          const left = `${a.hlc}:${a.site}`;
          const right = `${b.hlc}:${b.site}`;
          if (left < right) return -1;
          if (left > right) return 1;
          return 0;
        }),
      };
    case 4:
      return {
        typ: 4,
        values: [...state.values].sort((a, b) => {
          const left = `${a.hlc}:${a.site}:${JSON.stringify(a.val)}`;
          const right = `${b.hlc}:${b.site}:${JSON.stringify(b.val)}`;
          if (left < right) return -1;
          if (left > right) return 1;
          return 0;
        }),
      };
  }
}

function normalizeState(state: SqlEvalState): SqlEvalState {
  const schema: SqlSchema = Object.fromEntries(
    Object.entries(state.schema)
      .sort(([left], [right]) => (left < right ? -1 : left > right ? 1 : 0))
      .map(([table, tableSchema]) => [
        table,
        {
          pk: tableSchema.pk,
          partitionBy: tableSchema.partitionBy ?? null,
          columns: Object.fromEntries(
            Object.entries(tableSchema.columns)
              .sort(([left], [right]) => (left < right ? -1 : left > right ? 1 : 0))
              .map(([column, columnSchema]) => [column, { crdt: columnSchema.crdt }]),
          ),
        } satisfies SqlTableSchema,
      ]),
  );

  const rows = [...state.rows]
    .map((row): SqlEvalRowState => ({
      table: row.table,
      key: row.key,
      columns: Object.fromEntries(
        Object.entries(row.columns)
          .sort(([left], [right]) => (left < right ? -1 : left > right ? 1 : 0))
          .map(([column, columnState]) => [column, normalizeColumnState(columnState)]),
      ),
    }))
    .sort((left, right) => {
      const leftKey = rowStorageKey(left.table, left.key);
      const rightKey = rowStorageKey(right.table, right.key);
      if (leftKey < rightKey) return -1;
      if (leftKey > rightKey) return 1;
      return 0;
    });

  return { schema, rows };
}

function normalizeOutcome(outcome: SqlEvalOutcome): SqlEvalOutcome {
  const state = normalizeState(outcome.nextState);
  if (outcome.result.kind !== 'read') {
    return { result: outcome.result, nextState: state };
  }
  const rows = outcome.result.rows
    .map((row) =>
      normalizeJsonObject(
        Object.fromEntries(
          Object.entries(row).map(([column, value]) => [column, normalizeReadCell(value)]),
        ),
      ) as Record<string, unknown>,
    )
    .sort((left, right) => {
      const leftKey = JSON.stringify(left);
      const rightKey = JSON.stringify(right);
      if (leftKey < rightKey) return -1;
      if (leftKey > rightKey) return 1;
      return 0;
    });
  return {
    result: {
      kind: 'read',
      select: outcome.result.select,
      rows,
    },
    nextState: state,
  };
}

function toLeanSchema(schema: SqlSchema): LeanSchema {
  return Object.entries(schema).map(([table, tableSchema]) => ({
    table,
    pk: tableSchema.pk,
    partitionBy: tableSchema.partitionBy ?? null,
    columns: Object.entries(tableSchema.columns).map(([name, column]) => ({
      name,
      crdt: column.crdt,
    })),
  }));
}

function fromLeanSchema(schema: LeanSchema): SqlSchema {
  return Object.fromEntries(
    schema.map((table) => [
      table.table,
      {
        pk: table.pk,
        partitionBy: table.partitionBy ?? null,
        columns: Object.fromEntries(
          table.columns.map((column) => [
            column.name,
            { crdt: column.crdt as SqlTableSchema['columns'][string]['crdt'] },
          ]),
        ),
      } satisfies SqlTableSchema,
    ]),
  );
}

function toLeanState(state: SqlEvalState): LeanEvalState {
  const toEntries = (map: Record<string, number>): Array<{ site: string; n: number }> =>
    Object.entries(map)
      .map(([site, n]) => ({ site, n }))
      .sort((left, right) => (left.site < right.site ? -1 : left.site > right.site ? 1 : 0));

  return {
    rows: state.rows.map((row) => ({
      table: row.table,
      key: row.key,
      columns: Object.entries(row.columns).map(([column, columnState]) => ({
        column,
        state:
          columnState.typ === 1
            ? columnState
            : columnState.typ === 2
              ? {
                  typ: 2 as const,
                  inc: toEntries(columnState.inc),
                  dec: toEntries(columnState.dec),
                }
              : columnState,
      })),
    })),
  };
}

function fromLeanState(state: LeanEvalOutcome['nextState']): SqlEvalState {
  const fromEntries = (entries: Array<{ site: string; n: number }>): Record<string, number> =>
    Object.fromEntries(entries.map((entry) => [entry.site, entry.n]));

  return {
    schema: fromLeanSchema(state.schema),
    rows: state.rows.map((row) => ({
      table: row.table,
      key: row.key,
      columns: Object.fromEntries(
        row.columns.map((column) => [
          column.column,
          column.state.typ === 2
            ? {
                typ: 2 as const,
                inc: fromEntries(column.state.inc),
                dec: fromEntries(column.state.dec),
              }
            : (column.state as SqlEvalColumnState),
        ]),
      ),
    })),
  };
}

describe('DRT: SQL AST evaluation', () => {
  let client: LeanDrtClient | null = null;

  beforeAll(() => {
    if (leanBin) {
      client = new LeanDrtClient(leanBin);
    }
  });

  afterAll(() => {
    client?.close();
  });

  drt
    .prop(
      [arbSqlEvalCase],
      drtSeed === undefined ? { numRuns: drtRuns } : { numRuns: drtRuns, seed: drtSeed },
    )
    ('Lean sql_eval matches TypeScript evaluateSqlAst from SQL text', async (input) => {
      const parsed = parseSql(input.sql);

      let ts: SqlEvalOutcome | null = null;
      let tsError: string | null = null;
      try {
        ts = evaluateSqlAst(parsed, {
          state: input.state,
          context: input.context,
        });
      } catch (error) {
        tsError = error instanceof Error ? error.message : String(error);
      }

      if (tsError) {
        await expect(
          client!.sqlEval<{ result: LeanEvalOutcome }>(
            parsed,
            {
              schema: toLeanSchema(input.context.schema ?? input.state.schema),
              site: input.context.site,
              hlcSequence: input.context.hlcSequence,
              removeTags: input.context.removeTags ?? null,
            },
            toLeanState(input.state),
          ),
        ).rejects.toThrow();
        return;
      }

      const lean = await client!.sqlEval<{ result: LeanEvalOutcome }>(
        parsed,
        {
          schema: toLeanSchema(input.context.schema ?? input.state.schema),
          site: input.context.site,
          hlcSequence: input.context.hlcSequence,
          removeTags: input.context.removeTags ?? null,
        },
        toLeanState(input.state),
      );

      const leanOutcome: SqlEvalOutcome = {
        result: lean.result.result,
        nextState: fromLeanState(lean.result.nextState),
      };

      const normalizedLean = normalizeJsonObject(normalizeOutcome(leanOutcome));
      const normalizedTs = normalizeJsonObject(normalizeOutcome(ts!));
      expect(normalizedLean).toEqual(normalizedTs);
    }, drtTimeoutMs);
});
