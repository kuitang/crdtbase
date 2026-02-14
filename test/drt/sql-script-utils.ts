import { type SqlSchema, type SqlStatement, type SqlTableSchema } from '../../src/core/sql';
import {
  evaluateSqlAst,
  rowStorageKey,
  type SqlEvalColumnState,
  type SqlEvalContext,
  type SqlEvalOutcome,
  type SqlEvalRowState,
  type SqlEvalState,
} from '../../src/core/sqlEval';

export type LeanSchema = Array<{
  table: string;
  pk: string;
  partitionBy: string | null;
  columns: Array<{ name: string; crdt: string }>;
}>;

export type LeanEvalState = {
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

export type LeanScriptEvalOutcome = {
  outcomes: SqlEvalOutcome['result'][];
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

export function normalizeJsonObject(value: unknown): unknown {
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

export function normalizeState(state: SqlEvalState): SqlEvalState {
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

export function normalizeResult(result: SqlEvalOutcome['result']): SqlEvalOutcome['result'] {
  if (result.kind !== 'read') {
    return result;
  }
  const rows = result.rows
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
    kind: 'read',
    select: result.select,
    rows,
  };
}

export function normalizeScriptExecution(execution: {
  outcomes: SqlEvalOutcome['result'][];
  nextState: SqlEvalState;
}): {
  outcomes: SqlEvalOutcome['result'][];
  nextState: SqlEvalState;
} {
  return {
    outcomes: execution.outcomes.map((result) => normalizeResult(result)),
    nextState: normalizeState(execution.nextState),
  };
}

export function toLeanSchema(schema: SqlSchema): LeanSchema {
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

export function fromLeanSchema(schema: LeanSchema): SqlSchema {
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

export function toLeanState(state: SqlEvalState): LeanEvalState {
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

export function fromLeanState(state: LeanScriptEvalOutcome['nextState']): SqlEvalState {
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

export function evaluateSqlScriptTs(
  statements: SqlStatement[],
  input: {
    state: SqlEvalState;
    context: SqlEvalContext;
  },
): {
  outcomes: SqlEvalOutcome['result'][];
  nextState: SqlEvalState;
} {
  let state = input.state;
  let consumedHlc = 0;
  const outcomes: SqlEvalOutcome['result'][] = [];

  for (const statement of statements) {
    const outcome = evaluateSqlAst(statement, {
      state,
      context: {
        schema: state.schema,
        site: input.context.site,
        hlcSequence: input.context.hlcSequence?.slice(consumedHlc),
        removeTags: input.context.removeTags,
      },
    });
    outcomes.push(outcome.result);
    if (outcome.result.kind === 'write') {
      consumedHlc += outcome.result.ops.length;
    }
    state = outcome.nextState;
  }

  return {
    outcomes,
    nextState: state,
  };
}
