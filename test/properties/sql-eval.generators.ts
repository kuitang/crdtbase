import fc from 'fast-check';
import { type SqlEvalContext, type SqlEvalRowState, type SqlEvalState } from '../../src/core/sqlEval';
import { MODEL_TASKS_SCHEMA } from './sql.generators';

const RESERVED = new Set([
  'CREATE',
  'TABLE',
  'DROP',
  'INSERT',
  'INTO',
  'VALUES',
  'UPDATE',
  'SET',
  'SELECT',
  'FROM',
  'WHERE',
  'AND',
  'DELETE',
  'INC',
  'DEC',
  'ADD',
  'REMOVE',
  'TO',
  'BY',
  'TRUE',
  'FALSE',
  'NULL',
]);

const arbSiteId = fc.hexaString({ minLength: 8, maxLength: 8 });
const arbHlcHex = fc
  .hexaString({ minLength: 16, maxLength: 16 })
  .map((hex) => `0x${hex.toLowerCase()}`);

const arbPrimaryKey = fc.oneof(
  fc.string({ minLength: 1, maxLength: 12 }),
  fc.integer({ min: 0, max: 1_000_000 }),
);

const arbCounterNumber = fc.integer({ min: 0, max: 10_000 });

const arbComparableNumber = fc.integer({ min: -1_000, max: 1_000 });

const arbSqlLiteral = fc.oneof(
  fc.string({ maxLength: 24 }).map((value) => ({
    value,
    sql: `'${value.replace(/'/g, "''")}'`,
  })),
  arbComparableNumber.map((value) => ({
    value,
    sql: String(value),
  })),
  fc.boolean().map((value) => ({
    value,
    sql: value ? 'TRUE' : 'FALSE',
  })),
  fc.constant({ value: null, sql: 'NULL' }),
);

const arbLww = (valueArb: fc.Arbitrary<string | number | boolean | null>) =>
  fc.record({
    val: valueArb,
    hlc: arbHlcHex,
    site: arbSiteId,
  });

const arbPnCounter = fc.record({
  inc: fc.dictionary(arbSiteId, arbCounterNumber),
  dec: fc.dictionary(arbSiteId, arbCounterNumber),
});

const arbOrSet = fc
  .uniqueArray(
    fc.record({
      val: fc.string({ maxLength: 12 }),
      hlc: arbHlcHex,
      site: arbSiteId,
    }),
    {
      maxLength: 4,
      selector: (entry) => `${entry.hlc}:${entry.site}`,
    },
  )
  .chain((elements) =>
    fc
      .subarray(
        elements.map((entry) => ({ hlc: entry.hlc, site: entry.site })),
        { maxLength: elements.length },
      )
      .map((tombstones) => ({
        typ: 3 as const,
        elements: elements.map((entry) => ({
          val: entry.val,
          hlc: entry.hlc,
          site: entry.site,
        })),
        tombstones,
      })),
  );

const arbMv = fc
  .uniqueArray(
    fc.record({
      val: fc.string({ maxLength: 12 }),
      hlc: arbHlcHex,
      site: arbSiteId,
    }),
    {
      maxLength: 4,
      selector: (entry) => `${entry.hlc}:${entry.site}`,
    },
  )
  .map((values) => ({
    typ: 4 as const,
    values,
  }));

const arbEvalRowState: fc.Arbitrary<SqlEvalRowState> = fc
  .record({
    key: arbPrimaryKey,
    title: fc.option(arbLww(fc.string({ maxLength: 24 })), { nil: undefined }),
    done: fc.option(arbLww(fc.boolean()), { nil: undefined }),
    priority: fc.option(
      arbLww(fc.integer({ min: -100, max: 100 })),
      {
        nil: undefined,
      },
    ),
    points: fc.option(arbPnCounter, { nil: undefined }),
    tags: fc.option(arbOrSet, { nil: undefined }),
    status: fc.option(arbMv, { nil: undefined }),
    exists: fc.option(arbLww(fc.boolean()), { nil: undefined }),
  })
  .map((value) => {
    const columns: SqlEvalRowState['columns'] = {};
    if (value.title) columns.title = { typ: 1, ...value.title };
    if (value.done) columns.done = { typ: 1, ...value.done };
    if (value.priority) columns.priority = { typ: 1, ...value.priority };
    if (value.points) columns.points = { typ: 2, ...value.points };
    if (value.tags) columns.tags = value.tags;
    if (value.status) columns.status = value.status;
    if (value.exists) columns._exists = { typ: 1, ...value.exists };
    return {
      table: 'tasks',
      key: value.key,
      columns,
    };
  });

function cloneTasksSchema(): SqlEvalState['schema'] {
  return {
    tasks: {
      pk: 'id',
      partitionBy: MODEL_TASKS_SCHEMA.tasks.partitionBy ?? null,
      columns: Object.fromEntries(
        Object.entries(MODEL_TASKS_SCHEMA.tasks.columns).map(([name, column]) => [
          name,
          { crdt: column.crdt },
        ]),
      ),
    },
  };
}

const arbEvalState: fc.Arbitrary<SqlEvalState> = fc
  .uniqueArray(arbEvalRowState, {
    maxLength: 5,
    selector: (row) => `${row.table}:${String(row.key)}`,
  })
  .map((rows) => ({
    schema: cloneTasksSchema(),
    rows,
  }));

function renderValue(value: string | number | boolean | null): string {
  if (value === null) return 'NULL';
  if (typeof value === 'string') return `'${value.replace(/'/g, "''")}'`;
  if (typeof value === 'boolean') return value ? 'TRUE' : 'FALSE';
  return String(value);
}

const arbWhereById = arbPrimaryKey.map((id) => `id = ${renderValue(id)}`);

const arbSelectSql = fc.record({
  whereId: fc.option(arbWhereById, { nil: undefined }),
}).map(({ whereId }) => `SELECT * FROM tasks${whereId ? ` WHERE ${whereId}` : ''}`);

const arbInsertSql = fc
  .record({
    id: arbPrimaryKey,
    title: fc.option(fc.string({ maxLength: 24 }), { nil: undefined }),
    done: fc.option(fc.boolean(), { nil: undefined }),
    priority: fc.option(
      arbComparableNumber,
      { nil: undefined },
    ),
    points: fc.option(arbCounterNumber, { nil: undefined }),
    tags: fc.option(fc.string({ maxLength: 12 }), { nil: undefined }),
    status: fc.option(fc.string({ maxLength: 12 }), { nil: undefined }),
  })
  .filter(
    (value) =>
      value.title !== undefined ||
      value.done !== undefined ||
      value.priority !== undefined ||
      value.points !== undefined ||
      value.tags !== undefined ||
      value.status !== undefined,
  )
  .map((value) => {
    const columns: string[] = ['id'];
    const values: Array<string | number | boolean | null> = [value.id];
    if (value.title !== undefined) {
      columns.push('title');
      values.push(value.title);
    }
    if (value.done !== undefined) {
      columns.push('done');
      values.push(value.done);
    }
    if (value.priority !== undefined) {
      columns.push('priority');
      values.push(value.priority);
    }
    if (value.points !== undefined) {
      columns.push('points');
      values.push(value.points);
    }
    if (value.tags !== undefined) {
      columns.push('tags');
      values.push(value.tags);
    }
    if (value.status !== undefined) {
      columns.push('status');
      values.push(value.status);
    }
    return `INSERT INTO tasks (${columns.join(', ')}) VALUES (${values.map(renderValue).join(', ')})`;
  });

const arbUpdateSql = fc
  .record({
    whereId: arbWhereById,
    title: fc.option(fc.string({ maxLength: 24 }), { nil: undefined }),
    done: fc.option(fc.boolean(), { nil: undefined }),
    priority: fc.option(
      arbComparableNumber,
      { nil: undefined },
    ),
    status: fc.option(fc.string({ maxLength: 12 }), { nil: undefined }),
  })
  .filter(
    (value) =>
      value.title !== undefined ||
      value.done !== undefined ||
      value.priority !== undefined ||
      value.status !== undefined,
  )
  .map((value) => {
    const assignments: string[] = [];
    if (value.title !== undefined) assignments.push(`title = ${renderValue(value.title)}`);
    if (value.done !== undefined) assignments.push(`done = ${renderValue(value.done)}`);
    if (value.priority !== undefined) assignments.push(`priority = ${renderValue(value.priority)}`);
    if (value.status !== undefined) assignments.push(`status = ${renderValue(value.status)}`);
    return `UPDATE tasks SET ${assignments.join(', ')} WHERE ${value.whereId}`;
  });

const arbIncSql = fc.record({
  whereId: arbWhereById,
  amount: arbCounterNumber,
}).map((value) => `INC tasks.points BY ${value.amount} WHERE ${value.whereId}`);

const arbDecSql = fc.record({
  whereId: arbWhereById,
  amount: arbCounterNumber,
}).map((value) => `DEC tasks.points BY ${value.amount} WHERE ${value.whereId}`);

const arbAddSql = fc.record({
  whereId: arbWhereById,
  literal: arbSqlLiteral,
}).map((value) => `ADD ${value.literal.sql} TO tasks.tags WHERE ${value.whereId}`);

const arbRemoveSql = fc.record({
  whereId: arbWhereById,
  literal: arbSqlLiteral,
}).map((value) => `REMOVE ${value.literal.sql} FROM tasks.tags WHERE ${value.whereId}`);

const arbDeleteSql = arbWhereById.map((whereId) => `DELETE FROM tasks WHERE ${whereId}`);

const arbSqlText = fc.oneof(
  arbSelectSql,
  arbInsertSql,
  arbUpdateSql,
  arbIncSql,
  arbDecSql,
  arbAddSql,
  arbRemoveSql,
  arbDeleteSql,
);

const arbContext: fc.Arbitrary<SqlEvalContext> = fc.record({
  site: arbSiteId,
  hlcSequence: fc.array(arbHlcHex, { minLength: 24, maxLength: 40 }),
});

const arbTraceContext: fc.Arbitrary<SqlEvalContext> = fc.record({
  site: arbSiteId,
  hlcSequence: fc.array(arbHlcHex, { minLength: 64, maxLength: 160 }),
});

export type GeneratedSqlEvalCase = {
  sql: string;
  context: SqlEvalContext;
  state: SqlEvalState;
};

export const arbSqlEvalCase: fc.Arbitrary<GeneratedSqlEvalCase> = fc.record({
  sql: arbSqlText,
  context: arbContext,
  state: arbEvalState,
});

export type GeneratedSqlEvalTraceCase = {
  statements: string[];
  context: SqlEvalContext;
  state: SqlEvalState;
};

export const arbSqlEvalTraceCase: fc.Arbitrary<GeneratedSqlEvalTraceCase> = fc.record({
  statements: fc.array(arbSqlText, { minLength: 2, maxLength: 8 }),
  context: arbTraceContext,
  state: arbEvalState,
});
