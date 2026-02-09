import { Hlc, packHlc } from './hlc';
import { LwwRegister, mergeLww } from './crdt/lww';
import { MvRegister, MvRegisterValue, canonicalizeMvRegister, mergeMvRegister } from './crdt/mvRegister';
import { OrSet, OrSetElement, OrSetTag, canonicalizeOrSet, mergeOrSet } from './crdt/orSet';
import { PnCounter, applyPnCounterDelta, pnCounterValue } from './crdt/pnCounter';
import {
  AddStatement,
  CrdtOpPayload,
  DecStatement,
  DeleteStatement,
  EncodedCrdtOp,
  IncStatement,
  RemoveStatement,
  RemoveTagResolverInput,
  SetRemoveOpPayload,
  SetRemoveTag,
  SelectQueryPlan,
  SqlComparisonOp,
  SqlExecutionPlan,
  SqlPrimaryKey,
  SqlSchema,
  SqlStatement,
  SqlValue,
  UpdateStatement,
  buildSqlExecutionPlanFromStatement,
} from './sql';

export type RuntimeColumnState =
  | { typ: 1; state: LwwRegister<SqlValue> }
  | { typ: 2; state: PnCounter }
  | { typ: 3; state: OrSet<SqlValue> }
  | { typ: 4; state: MvRegister<SqlValue> };

export type RuntimeRowState = {
  table: string;
  key: SqlPrimaryKey;
  columns: Map<string, RuntimeColumnState>;
};

export type SqlEvalTag = {
  hlc: string;
  site: string;
};

export type SqlEvalColumnState =
  | { typ: 1; val: SqlValue; hlc: string; site: string }
  | { typ: 2; inc: Record<string, number>; dec: Record<string, number> }
  | {
      typ: 3;
      elements: Array<{ val: SqlValue; hlc: string; site: string }>;
      tombstones: SqlEvalTag[];
    }
  | {
      typ: 4;
      values: Array<{ val: SqlValue; hlc: string; site: string }>;
    };

export type SqlEvalRowState = {
  table: string;
  key: SqlPrimaryKey;
  columns: Record<string, SqlEvalColumnState>;
};

export type SqlEvalState = {
  schema: SqlSchema;
  rows: SqlEvalRowState[];
};

export type SqlEvalResult =
  | { kind: 'ddl_create_table'; table: string; schema: SqlSchema[string] }
  | { kind: 'ddl_drop_table'; table: string }
  | {
      kind: 'write';
      statementKind:
        | UpdateStatement['kind']
        | IncStatement['kind']
        | DecStatement['kind']
        | DeleteStatement['kind']
        | AddStatement['kind']
        | RemoveStatement['kind']
        | 'insert';
      ops: EncodedCrdtOp[];
    }
  | { kind: 'read'; select: SelectQueryPlan; rows: Record<string, unknown>[] };

export type SqlEvalOutcome = {
  result: SqlEvalResult;
  nextState: SqlEvalState;
};

export type SqlEvalContext = {
  schema?: SqlSchema;
  site?: string;
  hlcSequence?: string[];
  removeTags?: SetRemoveTag[];
};

export type MutableSqlEvalContext = {
  schema: SqlSchema;
  site?: string;
  nextHlc?: () => string;
  removeTags?: SetRemoveTag[];
};

function compareKeys(left: string, right: string): number {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function sortColumns(columns: Record<string, SqlEvalColumnState>): Record<string, SqlEvalColumnState> {
  return Object.fromEntries(
    Object.entries(columns).sort(([left], [right]) => compareKeys(left, right)),
  );
}

function cloneSchema(schema: SqlSchema): SqlSchema {
  const next: SqlSchema = {};
  for (const [table, tableSchema] of Object.entries(schema)) {
    next[table] = {
      pk: tableSchema.pk,
      partitionBy: tableSchema.partitionBy ?? null,
      columns: Object.fromEntries(
        Object.entries(tableSchema.columns).map(([name, column]) => [
          name,
          { crdt: column.crdt },
        ]),
      ),
    };
  }
  return next;
}

export function rowStorageKey(table: string, key: SqlPrimaryKey): string {
  return `${table}\u001f${String(key)}`;
}

export function encodeHlcHex(hlc: Hlc): string {
  return `0x${packHlc(hlc).toString(16)}`;
}

export function decodeHlcHex(encoded: string): Hlc {
  const normalized = encoded.startsWith('0x') ? encoded : `0x${encoded}`;
  const packed = BigInt(normalized);
  const wallMs = Number(packed >> 16n);
  const counter = Number(packed & 0xffffn);
  return { wallMs, counter };
}

function valueEquals(left: SqlValue, right: SqlValue): boolean {
  return Object.is(left, right);
}

function compareSqlScalars(left: SqlValue, right: SqlValue): number | null {
  if (typeof left === 'number' && typeof right === 'number') {
    return left === right ? 0 : left < right ? -1 : 1;
  }
  if (typeof left === 'string' && typeof right === 'string') {
    const cmp = left.localeCompare(right);
    return cmp === 0 ? 0 : cmp < 0 ? -1 : 1;
  }
  if (typeof left === 'boolean' && typeof right === 'boolean') {
    if (left === right) {
      return 0;
    }
    return left ? 1 : -1;
  }
  if (left === null && right === null) {
    return 0;
  }
  return null;
}

export function evalCondition(actual: unknown, op: SqlComparisonOp, expected: SqlValue): boolean {
  if (
    actual === null ||
    typeof actual === 'string' ||
    typeof actual === 'number' ||
    typeof actual === 'boolean'
  ) {
    const scalar = actual as SqlValue;
    const cmp = compareSqlScalars(scalar, expected);
    if (cmp === null) {
      return op === '!=';
    }
    switch (op) {
      case '=':
        return cmp === 0;
      case '!=':
        return cmp !== 0;
      case '<':
        return cmp < 0;
      case '>':
        return cmp > 0;
      case '<=':
        return cmp <= 0;
      case '>=':
        return cmp >= 0;
    }
  }

  if (Array.isArray(actual)) {
    if (op === '=') {
      return actual.some((value) => value === expected);
    }
    if (op === '!=') {
      return actual.every((value) => value !== expected);
    }
  }
  return false;
}

function assertCounterPayload(payload: CrdtOpPayload): payload is { d: 'inc' | 'dec'; n: number } {
  return (
    typeof payload === 'object' &&
    payload !== null &&
    'd' in payload &&
    'n' in payload &&
    (payload.d === 'inc' || payload.d === 'dec') &&
    typeof payload.n === 'number'
  );
}

function assertSetAddPayload(payload: CrdtOpPayload): payload is { a: 'add'; val: SqlValue } {
  return (
    typeof payload === 'object' &&
    payload !== null &&
    'a' in payload &&
    payload.a === 'add' &&
    'val' in payload
  );
}

function assertSetRemovePayload(payload: CrdtOpPayload): payload is SetRemoveOpPayload {
  return (
    typeof payload === 'object' &&
    payload !== null &&
    'a' in payload &&
    payload.a === 'rmv' &&
    'tags' in payload &&
    Array.isArray(payload.tags)
  );
}

function isSqlScalar(value: unknown): value is SqlValue {
  return (
    value === null ||
    typeof value === 'string' ||
    typeof value === 'number' ||
    typeof value === 'boolean'
  );
}

function serializeTag(tag: OrSetTag): SqlEvalTag {
  return { hlc: encodeHlcHex(tag.addHlc), site: tag.addSite };
}

function deserializeTag(tag: SqlEvalTag): OrSetTag {
  return { addHlc: decodeHlcHex(tag.hlc), addSite: tag.site };
}

export function runtimeColumnStateToEval(state: RuntimeColumnState): SqlEvalColumnState {
  switch (state.typ) {
    case 1:
      return {
        typ: 1,
        val: state.state.val,
        hlc: encodeHlcHex(state.state.hlc),
        site: state.state.site,
      };
    case 2:
      return {
        typ: 2,
        inc: state.state.inc,
        dec: state.state.dec,
      };
    case 3:
      return {
        typ: 3,
        elements: state.state.elements.map((element) => ({
          val: element.val,
          hlc: encodeHlcHex(element.tag.addHlc),
          site: element.tag.addSite,
        })),
        tombstones: state.state.tombstones.map(serializeTag),
      };
    case 4:
      return {
        typ: 4,
        values: state.state.values.map((value) => ({
          val: value.val,
          hlc: encodeHlcHex(value.hlc),
          site: value.site,
        })),
      };
  }
}

export function evalColumnStateToRuntime(state: SqlEvalColumnState): RuntimeColumnState {
  switch (state.typ) {
    case 1:
      return {
        typ: 1,
        state: {
          val: state.val,
          hlc: decodeHlcHex(state.hlc),
          site: state.site,
        },
      };
    case 2:
      return {
        typ: 2,
        state: {
          inc: state.inc,
          dec: state.dec,
        },
      };
    case 3:
      return {
        typ: 3,
        state: canonicalizeOrSet({
          elements: state.elements.map(
            (element): OrSetElement<SqlValue> => ({
              val: element.val,
              tag: { addHlc: decodeHlcHex(element.hlc), addSite: element.site },
            }),
          ),
          tombstones: state.tombstones.map(deserializeTag),
        }),
      };
    case 4:
      return {
        typ: 4,
        state: canonicalizeMvRegister({
          values: state.values.map(
            (value): MvRegisterValue<SqlValue> => ({
              val: value.val,
              hlc: decodeHlcHex(value.hlc),
              site: value.site,
            }),
          ),
        }),
      };
  }
}

export function runtimeRowsToEval(rows: Map<string, RuntimeRowState>): SqlEvalRowState[] {
  return [...rows.values()]
    .map((row) => ({
      table: row.table,
      key: row.key,
      columns: sortColumns(
        Object.fromEntries(
          [...row.columns.entries()].map(([column, state]) => [
            column,
            runtimeColumnStateToEval(state),
          ]),
        ),
      ),
    }))
    .sort((left, right) =>
      compareKeys(
        rowStorageKey(left.table, left.key),
        rowStorageKey(right.table, right.key),
      ),
    );
}

export function evalRowsToRuntime(rows: SqlEvalRowState[]): Map<string, RuntimeRowState> {
  const out = new Map<string, RuntimeRowState>();
  for (const row of rows) {
    const columns = new Map<string, RuntimeColumnState>();
    for (const [column, state] of Object.entries(row.columns)) {
      columns.set(column, evalColumnStateToRuntime(state));
    }
    out.set(rowStorageKey(row.table, row.key), {
      table: row.table,
      key: row.key,
      columns,
    });
  }
  return out;
}

export function materializeRow(row: RuntimeRowState): Record<string, unknown> {
  const values: Record<string, unknown> = {};
  for (const [column, state] of row.columns.entries()) {
    switch (state.typ) {
      case 1:
        values[column] = state.state.val;
        break;
      case 2:
        values[column] = pnCounterValue(state.state);
        break;
      case 3: {
        const seen = new Set<string>();
        const out: SqlValue[] = [];
        for (const element of state.state.elements) {
          const fingerprint = JSON.stringify(element.val);
          if (!seen.has(fingerprint)) {
            seen.add(fingerprint);
            out.push(element.val);
          }
        }
        values[column] = out;
        break;
      }
      case 4:
        values[column] =
          state.state.values.length === 1
            ? state.state.values[0]!.val
            : state.state.values.map((entry) => entry.val);
        break;
    }
  }
  return values;
}

export function resolveSetRemoveTagsFromRows(
  rows: Map<string, RuntimeRowState>,
  table: string,
  key: SqlPrimaryKey,
  column: string,
  value: SqlValue,
): SetRemoveTag[] {
  const row = rows.get(rowStorageKey(table, key));
  const state = row?.columns.get(column);
  if (!state || state.typ !== 3) {
    return [];
  }
  return state.state.elements
    .filter((element) => valueEquals(element.val, value))
    .map((element) => ({
      hlc: encodeHlcHex(element.tag.addHlc),
      site: element.tag.addSite,
    }));
}

export function applyCrdtOpToRows(
  rows: Map<string, RuntimeRowState>,
  op: EncodedCrdtOp,
): void {
  const key = rowStorageKey(op.tbl, op.key);
  const row =
    rows.get(key) ?? {
      table: op.tbl,
      key: op.key,
      columns: new Map<string, RuntimeColumnState>(),
    };
  const current = row.columns.get(op.col);
  const incomingHlc = decodeHlcHex(op.hlc);

  switch (op.typ) {
    case 1: {
      if (!isSqlScalar(op.val)) {
        throw new Error(`invalid LWW payload for ${op.tbl}.${op.col}`);
      }
      const incoming: LwwRegister<SqlValue> = {
        val: op.val,
        hlc: incomingHlc,
        site: op.site,
      };
      if (!current) {
        row.columns.set(op.col, { typ: 1, state: incoming });
      } else if (current.typ === 1) {
        row.columns.set(op.col, { typ: 1, state: mergeLww(current.state, incoming) });
      } else {
        throw new Error(
          `column '${op.tbl}.${op.col}' was previously typ ${current.typ}, got typ 1`,
        );
      }
      break;
    }
    case 2: {
      if (!assertCounterPayload(op.val)) {
        throw new Error(`invalid PN-Counter payload for ${op.tbl}.${op.col}`);
      }
      if (current && current.typ !== 2) {
        throw new Error(
          `column '${op.tbl}.${op.col}' was previously typ ${current.typ}, got typ 2`,
        );
      }
      const base = current?.typ === 2 ? current.state : { inc: {}, dec: {} };
      const merged = applyPnCounterDelta(base, op.site, op.val.d, op.val.n);
      row.columns.set(op.col, { typ: 2, state: merged });
      break;
    }
    case 3: {
      if (current && current.typ !== 3) {
        throw new Error(
          `column '${op.tbl}.${op.col}' was previously typ ${current.typ}, got typ 3`,
        );
      }
      const base = current?.typ === 3 ? current.state : { elements: [], tombstones: [] };
      if (assertSetAddPayload(op.val)) {
        const element: OrSetElement<SqlValue> = {
          val: op.val.val,
          tag: { addHlc: incomingHlc, addSite: op.site },
        };
        row.columns.set(op.col, {
          typ: 3,
          state: mergeOrSet(base, { elements: [element], tombstones: [] }),
        });
        break;
      }
      if (!assertSetRemovePayload(op.val)) {
        throw new Error(`invalid OR-Set payload for ${op.tbl}.${op.col}`);
      }
      const tombstones: OrSetTag[] = op.val.tags.map((tag) => ({
        addHlc: decodeHlcHex(tag.hlc),
        addSite: tag.site,
      }));
      row.columns.set(op.col, {
        typ: 3,
        state: mergeOrSet(base, { elements: [], tombstones }),
      });
      break;
    }
    case 4: {
      if (!isSqlScalar(op.val)) {
        throw new Error(`invalid MV-Register payload for ${op.tbl}.${op.col}`);
      }
      if (current && current.typ !== 4) {
        throw new Error(
          `column '${op.tbl}.${op.col}' was previously typ ${current.typ}, got typ 4`,
        );
      }
      const base = current?.typ === 4 ? current.state : { values: [] };
      const value: MvRegisterValue<SqlValue> = {
        val: op.val,
        hlc: incomingHlc,
        site: op.site,
      };
      row.columns.set(op.col, {
        typ: 4,
        state: mergeMvRegister(base, { values: [value] }),
      });
      break;
    }
    default:
      throw new Error(`unsupported CRDT op type ${(op as { typ: number }).typ}`);
  }

  rows.set(key, row);
}

export function runSelectPlan(
  plan: SelectQueryPlan,
  schema: SqlSchema,
  rowsState: Map<string, RuntimeRowState>,
): Record<string, unknown>[] {
  const tableSchema = schema[plan.table];
  if (!tableSchema) {
    throw new Error(`unknown table '${plan.table}'`);
  }
  const rows: Record<string, unknown>[] = [];
  for (const row of rowsState.values()) {
    if (row.table !== plan.table) {
      continue;
    }

    const materialized = materializeRow(row);
    materialized[tableSchema.pk] = row.key;
    if (
      !plan.filters.every((condition) =>
        evalCondition(materialized[condition.column], condition.op, condition.value),
      )
    ) {
      continue;
    }

    if (plan.columns === '*') {
      rows.push(materialized);
      continue;
    }

    const projected = Object.fromEntries(
      plan.columns.map((column) => [column, materialized[column]]),
    );
    rows.push(projected);
  }
  return rows;
}

export function evaluateSqlStatementMutable(
  statement: SqlStatement,
  rows: Map<string, RuntimeRowState>,
  context: MutableSqlEvalContext,
): SqlEvalResult {
  const resolver =
    context.removeTags === undefined
      ? ({ table, key, column, value }: RemoveTagResolverInput) =>
          resolveSetRemoveTagsFromRows(rows, table, key, column, value)
      : () => context.removeTags ?? [];
  const plan: SqlExecutionPlan = buildSqlExecutionPlanFromStatement(statement, {
    schema: context.schema,
    site: context.site,
    nextHlc: context.nextHlc,
    resolveSetRemoveTags: resolver,
  });

  switch (plan.kind) {
    case 'ddl_create_table':
      context.schema[plan.table] = plan.schema;
      return {
        kind: 'ddl_create_table',
        table: plan.table,
        schema: plan.schema,
      };
    case 'ddl_drop_table':
      delete context.schema[plan.table];
      return {
        kind: 'ddl_drop_table',
        table: plan.table,
      };
    case 'read':
      return {
        kind: 'read',
        select: plan.select,
        rows: runSelectPlan(plan.select, context.schema, rows),
      };
    case 'write':
      for (const op of plan.ops) {
        applyCrdtOpToRows(rows, op);
      }
      return {
        kind: 'write',
        statementKind: plan.statementKind,
        ops: plan.ops,
      };
  }
}

export function evaluateSqlAst(
  statement: SqlStatement,
  input: {
    state: SqlEvalState;
    context?: SqlEvalContext;
  },
): SqlEvalOutcome {
  const context = input.context ?? {};
  const schema = cloneSchema(context.schema ?? input.state.schema);
  const rows = evalRowsToRuntime(input.state.rows);

  const sequence = context.hlcSequence ? [...context.hlcSequence] : undefined;
  const nextHlc =
    sequence === undefined
      ? undefined
      : () => {
          if (sequence.length === 0) {
            throw new Error('nextHlc called too many times');
          }
          return sequence.shift()!;
        };

  const result = evaluateSqlStatementMutable(statement, rows, {
    schema,
    site: context.site,
    nextHlc,
    removeTags: context.removeTags,
  });

  return {
    result,
    nextState: {
      schema,
      rows: runtimeRowsToEval(rows),
    },
  };
}
