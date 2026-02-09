import fc from 'fast-check';

export type ModelSqlValue = string | number | boolean | null;

export type ModelComparisonOp = '=' | '!=' | '<' | '>' | '<=' | '>=';

export type ModelScalarType = 'STRING' | 'NUMBER' | 'BOOLEAN';

export type ModelColumnType =
  | { kind: 'scalar'; scalar: ModelScalarType }
  | { kind: 'lww'; scalar: ModelScalarType }
  | { kind: 'counter' }
  | { kind: 'set'; scalar: ModelScalarType }
  | { kind: 'register'; scalar: ModelScalarType };

export type ModelCreateColumn = {
  name: string;
  type: ModelColumnType;
  primaryKey?: true;
};

export type ModelWhereCondition = {
  column: string;
  op: ModelComparisonOp;
  value: ModelSqlValue;
};

export type ModelCreateTable = {
  kind: 'create_table';
  table: string;
  columns: ModelCreateColumn[];
  partitionBy?: string;
};

export type ModelDropTable = {
  kind: 'drop_table';
  table: string;
};

export type ModelInsert = {
  kind: 'insert';
  table: string;
  columns: string[];
  values: ModelSqlValue[];
};

export type ModelUpdate = {
  kind: 'update';
  table: string;
  assignments: Array<{ column: string; value: ModelSqlValue }>;
  where: ModelWhereCondition[];
};

export type ModelSelect = {
  kind: 'select';
  table: string;
  columns: '*' | string[];
  where?: ModelWhereCondition[];
};

export type ModelDelete = {
  kind: 'delete';
  table: string;
  where: ModelWhereCondition[];
};

export type ModelInc = {
  kind: 'inc';
  table: string;
  column: string;
  amount: number;
  where: ModelWhereCondition[];
};

export type ModelDec = {
  kind: 'dec';
  table: string;
  column: string;
  amount: number;
  where: ModelWhereCondition[];
};

export type ModelAdd = {
  kind: 'add';
  table: string;
  column: string;
  value: ModelSqlValue;
  where: ModelWhereCondition[];
};

export type ModelRemove = {
  kind: 'remove';
  table: string;
  column: string;
  value: ModelSqlValue;
  where: ModelWhereCondition[];
};

export type ModelSqlStatement =
  | ModelCreateTable
  | ModelDropTable
  | ModelInsert
  | ModelUpdate
  | ModelSelect
  | ModelDelete
  | ModelInc
  | ModelDec
  | ModelAdd
  | ModelRemove;

export type GeneratedSqlCase = {
  sql: string;
  expected: ModelSqlStatement;
};

export type GeneratedSelectSpec = {
  table: string;
  columns: '*' | string[];
  where?: ModelWhereCondition[];
};

export type ModelSelectQueryRoute =
  | { kind: 'single_partition'; partition: string }
  | { kind: 'all_partitions' };

export type ModelSelectQueryPlan = {
  table: string;
  columns: '*' | string[];
  partitionBy: string | null;
  route: ModelSelectQueryRoute;
  filters: ModelWhereCondition[];
};

export type GeneratedSelectPlanCase = {
  spec: GeneratedSelectSpec;
  sql: string;
  partitionBy?: string;
  expectedPlan: ModelSelectQueryPlan;
};

type RenderedLiteral = {
  value: ModelSqlValue;
  sql: string;
};

const RESERVED = new Set([
  'CREATE',
  'TABLE',
  'PARTITION',
  'BY',
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
  'LWW',
  'COUNTER',
  'REGISTER',
  'STRING',
  'NUMBER',
  'BOOLEAN',
  'PRIMARY',
  'KEY',
  'TRUE',
  'FALSE',
  'NULL',
]);

const arbIdentifier = fc
  .stringMatching(/^[a-z][a-z0-9_]{0,14}$/)
  .filter((identifier) => !RESERVED.has(identifier.toUpperCase()));

const arbIdentifierList = (minLength: number, maxLength: number): fc.Arbitrary<string[]> =>
  fc.uniqueArray(arbIdentifier, { minLength, maxLength });

const arbSqlNumber = fc.oneof(
  fc.integer({ min: -1_000_000, max: 1_000_000 }),
  fc
    .tuple(
      fc.integer({ min: -50_000, max: 50_000 }),
      fc.integer({ min: 1, max: 999_999 }),
    )
    .map(([whole, fractional]) => {
      const sign = whole < 0 ? -1 : 1;
      const absolute = Math.abs(whole) + fractional / 1_000_000;
      return sign * absolute;
    }),
);

const arbRenderedLiteral: fc.Arbitrary<RenderedLiteral> = fc.oneof(
  fc.string({ maxLength: 32 }).map((value) => ({
    value,
    sql: `'${value.replace(/'/g, "''")}'`,
  })),
  arbSqlNumber.map((value) => ({
    value,
    sql: String(value),
  })),
  fc.boolean().map((value) => ({
    value,
    sql: value ? 'TRUE' : 'FALSE',
  })),
  fc.constant({
    value: null,
    sql: 'NULL',
  }),
);

const arbComparisonOp: fc.Arbitrary<ModelComparisonOp> = fc.constantFrom(
  '=',
  '!=',
  '<',
  '>',
  '<=',
  '>=',
);

const arbCondition = fc
  .record({
    column: arbIdentifier,
    op: arbComparisonOp,
    literal: arbRenderedLiteral,
  })
  .map(({ column, op, literal }) => ({
    rendered: `${column} ${op} ${literal.sql}`,
    expected: {
      column,
      op,
      value: literal.value,
    } satisfies ModelWhereCondition,
  }));

const arbConditions = (minLength: number, maxLength: number) =>
  fc.array(arbCondition, { minLength, maxLength }).map((items) => ({
    rendered: items.map((item) => item.rendered).join(' AND '),
    expected: items.map((item) => item.expected),
  }));

const arbScalarType: fc.Arbitrary<ModelScalarType> = fc.constantFrom(
  'STRING',
  'NUMBER',
  'BOOLEAN',
);

const arbNonPrimaryColumnType: fc.Arbitrary<ModelColumnType> = fc.oneof(
  arbScalarType.map((scalar) => ({ kind: 'lww' as const, scalar })),
  fc.constant({ kind: 'counter' as const }),
  arbScalarType.map((scalar) => ({ kind: 'set' as const, scalar })),
  arbScalarType.map((scalar) => ({ kind: 'register' as const, scalar })),
);

const arbCreateColumns = fc
  .uniqueArray(
    fc.record({
      name: arbIdentifier,
      type: arbNonPrimaryColumnType,
      primaryKey: fc.boolean(),
    }),
    { minLength: 1, maxLength: 6, selector: (column) => column.name },
  )
  .map((columns) =>
    columns.map((column) =>
      column.primaryKey
        ? { name: column.name, type: column.type, primaryKey: true as const }
        : { name: column.name, type: column.type },
    ),
  );

function renderColumnType(type: ModelColumnType): string {
  switch (type.kind) {
    case 'scalar':
      return type.scalar;
    case 'lww':
      return `LWW<${type.scalar}>`;
    case 'counter':
      return 'COUNTER';
    case 'set':
      return `SET<${type.scalar}>`;
    case 'register':
      return `REGISTER<${type.scalar}>`;
  }
}

function renderWhere(conditions: ModelWhereCondition[] | undefined): string {
  if (!conditions || conditions.length === 0) return '';
  const parts = conditions.map((condition) => {
    const literal = renderLiteral(condition.value);
    return `${condition.column} ${condition.op} ${literal}`;
  });
  return ` WHERE ${parts.join(' AND ')}`;
}

function renderLiteral(value: ModelSqlValue): string {
  if (value === null) return 'NULL';
  if (typeof value === 'string') {
    return `'${value.replace(/'/g, "''")}'`;
  }
  if (typeof value === 'boolean') {
    return value ? 'TRUE' : 'FALSE';
  }
  return String(value);
}

const arbCreateTableCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    columns: arbCreateColumns,
    partitionBy: fc.option(arbIdentifier, { nil: undefined }),
  })
  .map(({ table, columns, partitionBy }) => {
    const renderedColumns = columns
      .map((column) =>
        column.primaryKey
          ? `${column.name} PRIMARY KEY`
          : `${column.name} ${renderColumnType(column.type)}`,
      )
      .join(', ');
    const partition = partitionBy ? ` PARTITION BY ${partitionBy}` : '';
    const sql = `CREATE TABLE ${table} (${renderedColumns})${partition}`;
    const normalizedColumns = columns.map((column) =>
      column.primaryKey
        ? ({ name: column.name, type: { kind: 'scalar', scalar: 'STRING' }, primaryKey: true as const })
        : column,
    );
    const expected = partitionBy
      ? ({ kind: 'create_table', table, columns: normalizedColumns, partitionBy } as const)
      : ({ kind: 'create_table', table, columns: normalizedColumns } as const);
    return { sql, expected };
  });

const arbDropTableCase: fc.Arbitrary<GeneratedSqlCase> = arbIdentifier.map((table) => ({
  sql: `DROP TABLE ${table}`,
  expected: {
    kind: 'drop_table',
    table,
  } satisfies ModelDropTable,
}));

const arbInsertCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    columns: arbIdentifierList(1, 6),
  })
  .chain(({ table, columns }) =>
    fc.array(arbRenderedLiteral, { minLength: columns.length, maxLength: columns.length }).map((lits) => {
      const values = lits.map((literal) => literal.value);
      const sql = `INSERT INTO ${table} (${columns.join(', ')}) VALUES (${lits
        .map((literal) => literal.sql)
        .join(', ')})`;
      return {
        sql,
        expected: {
          kind: 'insert',
          table,
          columns,
          values,
        } satisfies ModelInsert,
      };
    }),
  );

const arbUpdateCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    assignments: fc.uniqueArray(
      fc.record({
        column: arbIdentifier,
        literal: arbRenderedLiteral,
      }),
      { minLength: 1, maxLength: 6, selector: (assignment) => assignment.column },
    ),
    where: arbConditions(1, 4),
  })
  .map(({ table, assignments, where }) => {
    const renderedAssignments = assignments
      .map((assignment) => `${assignment.column} = ${assignment.literal.sql}`)
      .join(', ');
    const sql = `UPDATE ${table} SET ${renderedAssignments} WHERE ${where.rendered}`;
    return {
      sql,
      expected: {
        kind: 'update',
        table,
        assignments: assignments.map((assignment) => ({
          column: assignment.column,
          value: assignment.literal.value,
        })),
        where: where.expected,
      } satisfies ModelUpdate,
    };
  });

const arbSelectCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    columns: fc.oneof(fc.constant('*' as const), arbIdentifierList(1, 6)),
    where: fc.option(arbConditions(1, 4), { nil: undefined }),
  })
  .map(({ table, columns, where }) => {
    const projection = columns === '*' ? '*' : columns.join(', ');
    const expectedWhere = where?.expected;
    const sql = `SELECT ${projection} FROM ${table}${expectedWhere ? ` WHERE ${where!.rendered}` : ''}`;
    const expected = expectedWhere
      ? ({ kind: 'select', table, columns, where: expectedWhere } as const)
      : ({ kind: 'select', table, columns } as const);
    return { sql, expected };
  });

const arbDeleteCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    where: arbConditions(1, 4),
  })
  .map(({ table, where }) => ({
    sql: `DELETE FROM ${table} WHERE ${where.rendered}`,
    expected: {
      kind: 'delete',
      table,
      where: where.expected,
    } satisfies ModelDelete,
  }));

const arbIncCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    column: arbIdentifier,
    amount: fc.integer({ min: 0, max: 10_000 }),
    where: arbConditions(1, 4),
  })
  .map(({ table, column, amount, where }) => ({
    sql: `INC ${table}.${column} BY ${amount} WHERE ${where.rendered}`,
    expected: {
      kind: 'inc',
      table,
      column,
      amount,
      where: where.expected,
    } satisfies ModelInc,
  }));

const arbDecCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    column: arbIdentifier,
    amount: fc.integer({ min: 0, max: 10_000 }),
    where: arbConditions(1, 4),
  })
  .map(({ table, column, amount, where }) => ({
    sql: `DEC ${table}.${column} BY ${amount} WHERE ${where.rendered}`,
    expected: {
      kind: 'dec',
      table,
      column,
      amount,
      where: where.expected,
    } satisfies ModelDec,
  }));

const arbAddCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    column: arbIdentifier,
    literal: arbRenderedLiteral,
    where: arbConditions(1, 4),
  })
  .map(({ table, column, literal, where }) => ({
    sql: `ADD ${literal.sql} TO ${table}.${column} WHERE ${where.rendered}`,
    expected: {
      kind: 'add',
      table,
      column,
      value: literal.value,
      where: where.expected,
    } satisfies ModelAdd,
  }));

const arbRemoveCase: fc.Arbitrary<GeneratedSqlCase> = fc
  .record({
    table: arbIdentifier,
    column: arbIdentifier,
    literal: arbRenderedLiteral,
    where: arbConditions(1, 4),
  })
  .map(({ table, column, literal, where }) => ({
    sql: `REMOVE ${literal.sql} FROM ${table}.${column} WHERE ${where.rendered}`,
    expected: {
      kind: 'remove',
      table,
      column,
      value: literal.value,
      where: where.expected,
    } satisfies ModelRemove,
  }));

export const arbGeneratedSqlCase: fc.Arbitrary<GeneratedSqlCase> = fc.oneof(
  arbCreateTableCase,
  arbDropTableCase,
  arbInsertCase,
  arbUpdateCase,
  arbSelectCase,
  arbDeleteCase,
  arbIncCase,
  arbDecCase,
  arbAddCase,
  arbRemoveCase,
);

export const arbGeneratedSelectSpec: fc.Arbitrary<GeneratedSelectSpec> = fc
  .record({
    table: arbIdentifier,
    columns: fc.oneof(fc.constant('*' as const), arbIdentifierList(1, 6)),
    where: fc.option(arbConditions(1, 4), { nil: undefined }),
  })
  .map(({ table, columns, where }) => {
    const conditions = where?.expected;
    return conditions ? { table, columns, where: conditions } : { table, columns };
  });

export function renderSelectSpec(spec: GeneratedSelectSpec): string {
  const projection = spec.columns === '*' ? '*' : spec.columns.join(', ');
  return `SELECT ${projection} FROM ${spec.table}${renderWhere(spec.where)}`;
}

export function selectSpecToModel(spec: GeneratedSelectSpec): ModelSelect {
  return spec.where
    ? { kind: 'select', table: spec.table, columns: spec.columns, where: spec.where }
    : { kind: 'select', table: spec.table, columns: spec.columns };
}

function partitionValueToKey(value: ModelSqlValue): string {
  return value === null ? 'NULL' : String(value);
}

export function deriveModelSelectPlan(
  statement: ModelSelect,
  partitionBy: string | null | undefined,
): ModelSelectQueryPlan {
  const normalizedPartitionBy = partitionBy ?? null;
  const where = statement.where ? [...statement.where] : [];

  if (normalizedPartitionBy === null) {
    return {
      table: statement.table,
      columns: statement.columns,
      partitionBy: null,
      route: { kind: 'single_partition', partition: '_default' },
      filters: where,
    };
  }

  const index = where.findIndex(
    (condition) => condition.column === normalizedPartitionBy && condition.op === '=',
  );
  if (index < 0) {
    return {
      table: statement.table,
      columns: statement.columns,
      partitionBy: normalizedPartitionBy,
      route: { kind: 'all_partitions' },
      filters: where,
    };
  }

  const selected = where[index]!;
  return {
    table: statement.table,
    columns: statement.columns,
    partitionBy: normalizedPartitionBy,
    route: { kind: 'single_partition', partition: partitionValueToKey(selected.value) },
    filters: where.filter((_, conditionIndex) => conditionIndex !== index),
  };
}

export const arbGeneratedSelectPlanCase: fc.Arbitrary<GeneratedSelectPlanCase> = fc
  .record({
    spec: arbGeneratedSelectSpec,
    partitionBy: fc.option(arbIdentifier, { nil: undefined }),
  })
  .map(({ spec, partitionBy }) => {
    const sql = renderSelectSpec(spec);
    const expectedPlan = deriveModelSelectPlan(selectSpecToModel(spec), partitionBy);
    return partitionBy
      ? { spec, sql, partitionBy, expectedPlan }
      : { spec, sql, expectedPlan };
  });

export type ModelSqlSchema = Record<
  string,
  {
    pk: string;
    partitionBy?: string | null;
    columns: Record<string, { crdt: 'scalar' | 'lww' | 'pn_counter' | 'or_set' | 'mv_register' }>;
  }
>;

export type ModelEncodedCrdtOp =
  | {
      tbl: string;
      key: string | number;
      hlc: string;
      site: string;
      kind: 'row_exists';
      exists: boolean;
    }
  | {
      tbl: string;
      key: string | number;
      hlc: string;
      site: string;
      kind: 'cell_lww';
      col: string;
      val: ModelSqlValue;
    }
  | {
      tbl: string;
      key: string | number;
      hlc: string;
      site: string;
      kind: 'cell_counter';
      col: string;
      d: 'inc' | 'dec';
      n: number;
    }
  | {
      tbl: string;
      key: string | number;
      hlc: string;
      site: string;
      kind: 'cell_or_set_add';
      col: string;
      val: ModelSqlValue;
    }
  | {
      tbl: string;
      key: string | number;
      hlc: string;
      site: string;
      kind: 'cell_or_set_remove';
      col: string;
      tags: Array<{ hlc: string; site: string }>;
    }
  | {
      tbl: string;
      key: string | number;
      hlc: string;
      site: string;
      kind: 'cell_mv_register';
      col: string;
      val: ModelSqlValue;
    };

export type GeneratedWriteOpsCase = {
  sql: string;
  schema: ModelSqlSchema;
  site: string;
  hlcSequence: string[];
  removeTags?: Array<{ hlc: string; site: string }>;
  expectedOps: ModelEncodedCrdtOp[];
};

export const MODEL_TASKS_SCHEMA: ModelSqlSchema = {
  tasks: {
    pk: 'id',
    partitionBy: 'owner_id',
    columns: {
      id: { crdt: 'scalar' },
      owner_id: { crdt: 'lww' },
      title: { crdt: 'lww' },
      done: { crdt: 'lww' },
      priority: { crdt: 'lww' },
      points: { crdt: 'pn_counter' },
      tags: { crdt: 'or_set' },
      status: { crdt: 'mv_register' },
    },
  },
};

type WriteOpTemplate = Omit<ModelEncodedCrdtOp, 'hlc' | 'site'>;

type WriteCaseTemplate = {
  sql: string;
  templates: WriteOpTemplate[];
  removeTags?: Array<{ hlc: string; site: string }>;
};

const arbSiteId = fc.hexaString({ minLength: 8, maxLength: 8 });
const arbHlcHex = fc
  .hexaString({ minLength: 1, maxLength: 16 })
  .map((hex) => `0x${hex.toLowerCase()}`);
const arbPrimaryKey = fc.oneof(
  fc.string({ minLength: 1, maxLength: 12 }),
  fc.integer({ min: 0, max: 1_000_000 }),
);

const arbSmallString = fc.string({ minLength: 1, maxLength: 24 });
const arbTag = fc.record({
  hlc: arbHlcHex,
  site: arbSiteId,
});

function withMeta(templateArb: fc.Arbitrary<WriteCaseTemplate>): fc.Arbitrary<GeneratedWriteOpsCase> {
  return templateArb.chain((template) =>
    fc
      .record({
        site: arbSiteId,
        hlcSequence: fc.array(arbHlcHex, {
          minLength: template.templates.length,
          maxLength: template.templates.length,
        }),
      })
      .map(({ site, hlcSequence }) => ({
        sql: template.sql,
        schema: MODEL_TASKS_SCHEMA,
        site,
        hlcSequence,
        removeTags: template.removeTags,
        expectedOps: template.templates.map((op, index) => ({
          ...op,
          hlc: hlcSequence[index]!,
          site,
        })),
      })),
  );
}

function whereById(id: string | number, extraOwner: string | undefined): string {
  if (!extraOwner) {
    return `id = ${renderLiteral(id)}`;
  }
  return `id = ${renderLiteral(id)} AND owner_id = ${renderLiteral(extraOwner)}`;
}

const arbInsertWriteCaseTemplate: fc.Arbitrary<WriteCaseTemplate> = fc
  .record({
    id: arbPrimaryKey,
    ownerId: fc.option(arbSmallString, { nil: undefined }),
    title: fc.option(arbSmallString, { nil: undefined }),
    done: fc.option(fc.boolean(), { nil: undefined }),
    priority: fc.option(fc.integer({ min: -100, max: 100 }), { nil: undefined }),
    points: fc.option(fc.integer({ min: 0, max: 10_000 }), { nil: undefined }),
    tags: fc.option(arbSmallString, { nil: undefined }),
    status: fc.option(arbSmallString, { nil: undefined }),
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
    const values: ModelSqlValue[] = [value.id];
    const templates: WriteOpTemplate[] = [
      { tbl: 'tasks', key: value.id, kind: 'row_exists', exists: true },
    ];

    if (value.ownerId !== undefined) {
      columns.push('owner_id');
      values.push(value.ownerId);
      templates.push({
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_lww',
        col: 'owner_id',
        val: value.ownerId,
      });
    }
    if (value.title !== undefined) {
      columns.push('title');
      values.push(value.title);
      templates.push({
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_lww',
        col: 'title',
        val: value.title,
      });
    }
    if (value.done !== undefined) {
      columns.push('done');
      values.push(value.done);
      templates.push({
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_lww',
        col: 'done',
        val: value.done,
      });
    }
    if (value.priority !== undefined) {
      columns.push('priority');
      values.push(value.priority);
      templates.push({
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_lww',
        col: 'priority',
        val: value.priority,
      });
    }
    if (value.points !== undefined) {
      columns.push('points');
      values.push(value.points);
      templates.push({
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_counter',
        col: 'points',
        d: 'inc',
        n: value.points,
      });
    }
    if (value.tags !== undefined) {
      columns.push('tags');
      values.push(value.tags);
      templates.push({
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_or_set_add',
        col: 'tags',
        val: value.tags,
      });
    }
    if (value.status !== undefined) {
      columns.push('status');
      values.push(value.status);
      templates.push({
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_mv_register',
        col: 'status',
        val: value.status,
      });
    }

    return {
      sql: `INSERT INTO tasks (${columns.join(', ')}) VALUES (${values.map(renderLiteral).join(', ')})`,
      templates,
    };
  });

const arbUpdateWriteCaseTemplate: fc.Arbitrary<WriteCaseTemplate> = fc
  .record({
    id: arbPrimaryKey,
    ownerId: fc.option(arbSmallString, { nil: undefined }),
    title: fc.option(arbSmallString, { nil: undefined }),
    done: fc.option(fc.boolean(), { nil: undefined }),
    priority: fc.option(fc.integer({ min: -100, max: 100 }), { nil: undefined }),
    status: fc.option(arbSmallString, { nil: undefined }),
  })
  .filter(
    (value) =>
      value.title !== undefined ||
      value.done !== undefined ||
      value.priority !== undefined ||
      value.status !== undefined,
  )
  .map((value) => {
    const assignments: Array<{ text: string; template: WriteOpTemplate }> = [];
    if (value.title !== undefined) {
      assignments.push({
        text: `title = ${renderLiteral(value.title)}`,
        template: {
          tbl: 'tasks',
          key: value.id,
          kind: 'cell_lww',
          col: 'title',
          val: value.title,
        },
      });
    }
    if (value.done !== undefined) {
      assignments.push({
        text: `done = ${renderLiteral(value.done)}`,
        template: {
          tbl: 'tasks',
          key: value.id,
          kind: 'cell_lww',
          col: 'done',
          val: value.done,
        },
      });
    }
    if (value.priority !== undefined) {
      assignments.push({
        text: `priority = ${renderLiteral(value.priority)}`,
        template: {
          tbl: 'tasks',
          key: value.id,
          kind: 'cell_lww',
          col: 'priority',
          val: value.priority,
        },
      });
    }
    if (value.status !== undefined) {
      assignments.push({
        text: `status = ${renderLiteral(value.status)}`,
        template: {
          tbl: 'tasks',
          key: value.id,
          kind: 'cell_mv_register',
          col: 'status',
          val: value.status,
        },
      });
    }

    const templates: WriteOpTemplate[] = [
      { tbl: 'tasks', key: value.id, kind: 'row_exists', exists: true },
      ...assignments.map((item) => item.template),
    ];
    return {
      sql: `UPDATE tasks SET ${assignments.map((item) => item.text).join(', ')} WHERE ${whereById(
        value.id,
        value.ownerId,
      )}`,
      templates,
    };
  });

const arbIncWriteCaseTemplate: fc.Arbitrary<WriteCaseTemplate> = fc
  .record({
    id: arbPrimaryKey,
    ownerId: fc.option(arbSmallString, { nil: undefined }),
    amount: fc.integer({ min: 0, max: 10_000 }),
  })
  .map((value) => ({
    sql: `INC tasks.points BY ${value.amount} WHERE ${whereById(value.id, value.ownerId)}`,
    templates: [
      { tbl: 'tasks', key: value.id, kind: 'row_exists', exists: true },
      {
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_counter',
        col: 'points',
        d: 'inc',
        n: value.amount,
      },
    ],
  }));

const arbDecWriteCaseTemplate: fc.Arbitrary<WriteCaseTemplate> = fc
  .record({
    id: arbPrimaryKey,
    ownerId: fc.option(arbSmallString, { nil: undefined }),
    amount: fc.integer({ min: 0, max: 10_000 }),
  })
  .map((value) => ({
    sql: `DEC tasks.points BY ${value.amount} WHERE ${whereById(value.id, value.ownerId)}`,
    templates: [
      { tbl: 'tasks', key: value.id, kind: 'row_exists', exists: true },
      {
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_counter',
        col: 'points',
        d: 'dec',
        n: value.amount,
      },
    ],
  }));

const arbAddWriteCaseTemplate: fc.Arbitrary<WriteCaseTemplate> = fc
  .record({
    id: arbPrimaryKey,
    ownerId: fc.option(arbSmallString, { nil: undefined }),
    value: arbSmallString,
  })
  .map((value) => ({
    sql: `ADD ${renderLiteral(value.value)} TO tasks.tags WHERE ${whereById(value.id, value.ownerId)}`,
    templates: [
      { tbl: 'tasks', key: value.id, kind: 'row_exists', exists: true },
      {
        tbl: 'tasks',
        key: value.id,
        kind: 'cell_or_set_add',
        col: 'tags',
        val: value.value,
      },
    ],
  }));

const arbRemoveWriteCaseTemplate: fc.Arbitrary<WriteCaseTemplate> = fc
  .record({
    id: arbPrimaryKey,
    ownerId: fc.option(arbSmallString, { nil: undefined }),
    value: arbSmallString,
    tags: fc.array(arbTag, { minLength: 0, maxLength: 4 }),
  })
  .map((value) => ({
    sql: `REMOVE ${renderLiteral(value.value)} FROM tasks.tags WHERE ${whereById(
      value.id,
      value.ownerId,
    )}`,
    removeTags: value.tags,
    templates:
      value.tags.length > 0
        ? [
            { tbl: 'tasks', key: value.id, kind: 'row_exists', exists: true },
            {
              tbl: 'tasks',
              key: value.id,
              kind: 'cell_or_set_remove',
              col: 'tags',
              tags: value.tags,
            },
          ]
        : [],
  }));

const arbDeleteWriteCaseTemplate: fc.Arbitrary<WriteCaseTemplate> = fc
  .record({
    id: arbPrimaryKey,
    ownerId: fc.option(arbSmallString, { nil: undefined }),
  })
  .map((value) => ({
    sql: `DELETE FROM tasks WHERE ${whereById(value.id, value.ownerId)}`,
    templates: [{ tbl: 'tasks', key: value.id, kind: 'row_exists', exists: false }],
  }));

export const arbGeneratedWriteOpsCase: fc.Arbitrary<GeneratedWriteOpsCase> = withMeta(
  fc.oneof(
    arbInsertWriteCaseTemplate,
    arbUpdateWriteCaseTemplate,
    arbIncWriteCaseTemplate,
    arbDecWriteCaseTemplate,
    arbAddWriteCaseTemplate,
    arbRemoveWriteCaseTemplate,
    arbDeleteWriteCaseTemplate,
  ),
);
