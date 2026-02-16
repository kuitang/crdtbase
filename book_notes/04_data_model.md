# Chapter 4: Data Model and Storage Layer

## Overview

CRDTBase is a CRDT-native database that maps a relational table/row/column model
onto conflict-free replicated data types. Every column in every row carries its
own CRDT state, enabling offline writes that merge deterministically without
coordination. The system persists everything as MessagePack-encoded binary files,
replicated through either an HTTP server or S3-compatible object storage (Tigris).

This chapter traces the complete data model from the SQL surface through CRDT
semantics to physical storage, and examines the correctness guarantees at each
layer.

---

## 1. Schema: Tables, Columns, and CRDT Types

### 1.1 The Schema Type

The in-memory schema is a record mapping table names to table schemas:

```typescript
// src/core/sql.ts:199-207
export type SqlColumnCrdt = 'scalar' | 'lww' | 'pn_counter' | 'or_set' | 'mv_register';

export type SqlTableSchema = {
  pk: string;
  partitionBy?: string | null;
  columns: Record<string, { crdt: SqlColumnCrdt }>;
};

export type SqlSchema = Record<string, SqlTableSchema>;
```

Each table has:
- **One primary key column** (`pk`), always typed `scalar` internally.
- **An optional partition key** (`partitionBy`), naming a column used to route
  rows into segment files. If null, all rows go into partition `"_default"`.
- **A column map** where each non-PK column has a CRDT type tag.

### 1.2 The Information Schema

Schema metadata is itself stored as CRDT-replicated rows in two virtual tables.
This design ensures schema changes propagate through the same replication
pipeline as data changes, achieving eventual consistency for DDL across replicas.

```typescript
// src/core/sql.ts:245-268
export const INFORMATION_SCHEMA_TABLES = 'information_schema.tables';
export const INFORMATION_SCHEMA_COLUMNS = 'information_schema.columns';

const INFORMATION_SCHEMA_METADATA: Readonly<Record<string, SqlTableSchema>> = {
  [INFORMATION_SCHEMA_TABLES]: {
    pk: 'table_name',
    partitionBy: null,
    columns: {
      table_name: { crdt: 'scalar' },
      pk_column: { crdt: 'lww' },
      partition_by: { crdt: 'lww' },
    },
  },
  [INFORMATION_SCHEMA_COLUMNS]: {
    pk: 'column_id',
    partitionBy: null,
    columns: {
      column_id: { crdt: 'scalar' },
      table_name: { crdt: 'lww' },
      column_name: { crdt: 'lww' },
      crdt_kind: { crdt: 'lww' },
    },
  },
};
```

The information schema tables have the following logical DDL:

```sql
-- Conceptual DDL (not user-executable)
CREATE TABLE information_schema.tables (
  table_name   PRIMARY KEY,    -- user table name
  pk_column    LWW<STRING>,    -- name of the PK column
  partition_by LWW<STRING>     -- partition key column (or NULL)
);

CREATE TABLE information_schema.columns (
  column_id    PRIMARY KEY,    -- composite key: "table:column"
  table_name   LWW<STRING>,    -- owning table name
  column_name  LWW<STRING>,    -- column name
  crdt_kind    LWW<STRING>     -- one of: scalar, lww, pn_counter, or_set, mv_register
);
```

The `column_id` primary key is a composite string `"table:column"`:

```typescript
// src/core/sql.ts:1137-1139
function columnId(table: string, column: string): string {
  return `${table}:${column}`;
}
```

Because all information schema columns use LWW registers, concurrent DDL from
different replicas resolves deterministically: the last-writer-wins semantics
produce the same schema on every replica after convergence.

### 1.3 DDL: CREATE TABLE

The SQL parser accepts CRDT-annotated column types:

```sql
CREATE TABLE tasks (
  id       PRIMARY KEY,
  title    LWW<STRING>,
  done     LWW<BOOLEAN>,
  priority LWW<NUMBER>,
  points   COUNTER,
  tags     SET<STRING>,
  status   REGISTER<STRING>
) PARTITION BY owner_id;
```

The parser (`src/core/sql.ts:452-467`) converts `PRIMARY KEY` to the internal
`{ kind: 'scalar', scalar: 'STRING' }` representation. Non-PK columns must use
`LWW<T>`, `COUNTER`, `SET<T>`, or `REGISTER<T>`.

The function `tableSchemaFromCreate` (`src/core/sql.ts:955-983`) converts the
parsed AST into the runtime `SqlTableSchema`:

```typescript
// src/core/sql.ts:955-983
export function tableSchemaFromCreate(statement: CreateTableStatement): SqlTableSchema {
  const primaryKeys = statement.columns.filter((column) => column.primaryKey);
  if (primaryKeys.length !== 1) {
    throw new Error(
      `CREATE TABLE ${statement.table} must declare exactly one PRIMARY KEY column`,
    );
  }
  const columns: SqlTableSchema['columns'] = {};
  const pkName = primaryKeys[0]!.name;
  for (const column of statement.columns) {
    if (columns[column.name]) {
      throw new Error(`CREATE TABLE ${statement.table} has duplicate column '${column.name}'`);
    }
    if (column.type.kind === 'scalar' && column.name !== pkName) {
      columns[column.name] = { crdt: 'lww' };
      continue;
    }
    columns[column.name] = { crdt: columnTypeToSchema(column.type) };
  }
  return { pk: pkName, partitionBy: statement.partitionBy ?? null, columns };
}
```

**Schema-as-CRDT-ops**: When a client executes `CREATE TABLE`, the client-side
planner (`buildClientSqlExecutionPlanFromStatement`, line 1646) does not emit a
traditional DDL plan. Instead, it calls `planCreateTableSchemaMutation`
(line 1231), which generates LWW ops against the information schema tables:

```typescript
// src/core/sql.ts:1141-1185
function createInformationSchemaTableOps(
  context: CrdtOpGenerationContext,
  table: string,
  schema: SqlTableSchema,
): EncodedCrdtOp[] {
  const ops: EncodedCrdtOp[] = [
    createRowExistsOp(context, INFORMATION_SCHEMA_TABLES, table, true),
    {
      ...createOp(context, INFORMATION_SCHEMA_TABLES, table),
      kind: 'cell_lww',
      col: 'pk_column',
      val: schema.pk,
    },
    {
      ...createOp(context, INFORMATION_SCHEMA_TABLES, table),
      kind: 'cell_lww',
      col: 'partition_by',
      val: schema.partitionBy ?? null,
    },
  ];
  const columnNames = Object.keys(schema.columns).sort();
  for (const name of columnNames) {
    const key = columnId(table, name);
    ops.push(createRowExistsOp(context, INFORMATION_SCHEMA_COLUMNS, key, true));
    ops.push({ ...createOp(context, INFORMATION_SCHEMA_COLUMNS, key), kind: 'cell_lww', col: 'table_name', val: table });
    ops.push({ ...createOp(context, INFORMATION_SCHEMA_COLUMNS, key), kind: 'cell_lww', col: 'column_name', val: name });
    ops.push({ ...createOp(context, INFORMATION_SCHEMA_COLUMNS, key), kind: 'cell_lww', col: 'crdt_kind', val: schema.columns[name]!.crdt });
  }
  return ops;
}
```

A `CREATE TABLE tasks` with 6 columns therefore generates: 3 ops for
`information_schema.tables` (row_exists + pk_column + partition_by) plus
4 ops per column for `information_schema.columns` (row_exists + table_name +
column_name + crdt_kind) = 3 + 6*4 = 27 CRDT ops. These ops flow through
the standard replication pipeline, so other replicas learn the schema through
normal sync.

**Idempotent CREATE**: If the table already exists with an identical schema,
`planCreateTableSchemaMutation` returns zero ops (line 1241-1242). If it
conflicts (same name, different schema), an error is thrown.

### 1.4 DDL: ALTER TABLE ADD COLUMN

Schema evolution is supported through `ALTER TABLE ADD COLUMN`:

```sql
ALTER TABLE tasks ADD COLUMN assignee LWW<STRING>;
```

The planner (`planAlterAddColumnSchemaMutation`, line 1249) generates column-
scoped information schema ops:

```typescript
// src/core/sql.ts:1249-1276
function planAlterAddColumnSchemaMutation(
  statement: AlterTableAddColumnStatement,
  context: CrdtOpGenerationContext,
): EncodedCrdtOp[] {
  // ...
  const newCrdt = columnTypeToSchema(statement.column.type);
  const existingColumn = tableSchema.columns[statement.column.name];
  if (existingColumn) {
    if (existingColumn.crdt === newCrdt) {
      return [];   // idempotent: column already exists with matching type
    }
    throw new Error(/* conflict */);
  }
  return createInformationSchemaColumnOps(context, statement.table, statement.column.name, newCrdt);
}
```

Like `CREATE TABLE`, this generates 4 LWW ops against `information_schema.columns`.
The schema is **append-only**: there is no `DROP COLUMN` and no way to change a
column's CRDT type after creation.

### 1.5 DDL: DROP TABLE

`DROP TABLE` is supported at the eval layer (`evaluateSqlStatementMutable`,
line 723-728) but the client-side planner explicitly rejects it:

```typescript
// src/core/sql.ts:1667-1670
case 'drop_table':
  throw new Error(
    `DROP TABLE is not allowed; schema is append-only and supports CREATE TABLE + ALTER TABLE ADD COLUMN only`,
  );
```

This means `DROP TABLE` is available for testing infrastructure but not for
production clients. The schema is designed to grow monotonically, ensuring that
concurrent schema evolution always converges.

### 1.6 Schema Materialization from Rows

When a client loads state from disk or receives replicated ops, the schema is
reconstituted from the information schema rows:

```typescript
// src/core/sqlEval.ts:420-507
export function materializeSchemaFromRows(rows: Map<string, RuntimeRowState>): SqlSchema {
  const tables = new Map<string, { pk: string | null; partitionBy: string | null; columns: Record<string, { crdt: SqlColumnCrdt }> }>();

  // Pass 1: read information_schema.tables rows
  for (const row of rows.values()) {
    if (row.table !== INFORMATION_SCHEMA_TABLES || rowIsDeleted(row)) continue;
    // Extract pk_column and partition_by LWW values
    // ...
  }

  // Pass 2: read information_schema.columns rows
  for (const row of rows.values()) {
    if (row.table !== INFORMATION_SCHEMA_COLUMNS || rowIsDeleted(row)) continue;
    // Extract table_name, column_name, crdt_kind LWW values
    // ...
  }

  // Assemble only tables with a valid PK column
  const schema: SqlSchema = {};
  for (const [tableName, entry] of tables.entries()) {
    if (!entry.pk) continue;
    schema[tableName] = { pk: entry.pk, partitionBy: entry.partitionBy, columns: entry.columns };
  }
  return schema;
}
```

Both `NodeCrdtClient` (line 249-255) and `BrowserCrdtClient` (line 202-208)
call `refreshSchemaFromRows()` after every write and pull, keeping the in-memory
schema in sync with CRDT state. The schema is also persisted to `schema.bin`
via MessagePack for fast startup.

### 1.7 Effective Schema for Query Planning

When planning SELECT queries, the schema is augmented with the information schema
metadata so users can query the catalog:

```typescript
// src/core/sql.ts:1296-1301
export function buildEffectiveSchemaForPlanning(schema: SqlSchema): SqlSchema {
  return {
    ...buildInformationSchemaMetadata(),
    ...schema,
  };
}
```

This allows `SELECT * FROM information_schema.tables;` and
`SELECT * FROM information_schema.columns;` to work as expected.

---

## 2. Row and Column Representation

### 2.1 Runtime Row State

The in-memory representation during query execution lives in `src/core/sqlEval.ts`:

```typescript
// src/core/sqlEval.ts:29-39
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
```

Rows are keyed in a `Map<string, RuntimeRowState>` using a composite storage
key:

```typescript
// src/core/sqlEval.ts:138-140
export function rowStorageKey(table: string, key: SqlPrimaryKey): string {
  return `${table}\u001f${String(key)}`;
}
```

The `\u001f` (unit separator) character prevents collisions between table names
and key values. The row's primary key value is carried in `RuntimeRowState.key`,
not as a column in the `columns` map.

### 2.2 Row Existence: The `_exists` Column

DELETE is implemented as a tombstone. A hidden LWW register column named
`_exists` tracks whether a row is alive:

```typescript
// src/core/sqlEval.ts:541-558
case 'row_exists': {
  const current = row.columns.get('_exists');
  const incoming: LwwRegister<SqlValue> = {
    val: op.exists,
    hlc: incomingHlc,
    site: op.site,
  };
  if (!current) {
    row.columns.set('_exists', { typ: 1, state: incoming });
  } else if (current.typ === 1) {
    row.columns.set('_exists', { typ: 1, state: mergeLww(current.state, incoming) });
  }
  // ...
}
```

Every write operation (INSERT, UPDATE, INC, DEC, ADD) emits a `row_exists: true`
op as the first op. DELETE emits `row_exists: false`. The LWW merge semantics
mean the latest-timestamped existence event wins.

Reads filter deleted rows:

```typescript
// src/core/sqlEval.ts:670-673
const exists = row.columns.get('_exists');
if (exists && exists.typ === 1 && exists.state.val === false) {
  continue;
}
```

### 2.3 Serialized Row State (Eval Format)

For persistence and serialization, there is a parallel "eval" format that uses
hex-encoded HLC strings rather than structured `Hlc` objects:

```typescript
// src/core/sqlEval.ts:46-63
export type SqlEvalColumnState =
  | { typ: 1; val: SqlValue; hlc: string; site: string }
  | { typ: 2; inc: Record<string, number>; dec: Record<string, number> }
  | { typ: 3; elements: Array<{ val: SqlValue; hlc: string; site: string }>;
      tombstones: SqlEvalTag[] }
  | { typ: 4; values: Array<{ val: SqlValue; hlc: string; site: string }> };

export type SqlEvalRowState = {
  table: string;
  key: SqlPrimaryKey;
  columns: Record<string, SqlEvalColumnState>;
};
```

The conversion functions `runtimeColumnStateToEval` and `evalColumnStateToRuntime`
bridge the two representations. The eval format is what gets encoded to
MessagePack for persistence.

---

## 3. The Four CRDT Types

### 3.1 LWW Register (tag = 1)

```typescript
// src/core/crdt/lww.ts:3-7
export type LwwRegister<T> = {
  val: T;
  hlc: Hlc;
  site: string;
};
```

**Merge**: The register with the higher `(hlc, site)` pair wins. If both are
identical, the payloads must also be identical (invariant enforced by
`assertLwwEventConsistency`):

```typescript
// src/core/crdt/lww.ts:23-30
export function mergeLww<T>(a: LwwRegister<T>, b: LwwRegister<T>): LwwRegister<T> {
  assertLwwEventConsistency(a, b);
  const cmp = compareWithSite(a.hlc, a.site, b.hlc, b.site);
  if (cmp >= 0) { return a; }
  return b;
}
```

**Safety invariant**: Equal `(hlc, site)` implies same payload. The spec
(section 5.1) lists the conditions under which this can fail: site ID collision,
clock state loss on restart, snapshot restoration without fencing.

The `LwwConflictGuard` class (`src/core/crdt/lwwConflictGuard.ts`) can detect
violations at ingest time by fingerprinting payloads keyed by
`(table, key, col, site, hlc)`.

### 3.2 PN-Counter (tag = 2)

```typescript
// src/core/crdt/pnCounter.ts:1-6
export type SiteCountMap = Record<string, number>;
export type PnCounter = {
  inc: SiteCountMap;
  dec: SiteCountMap;
};
```

**Merge**: Per-site max for both `inc` and `dec` maps independently:

```typescript
// src/core/crdt/pnCounter.ts:49-56
export function mergePnCounter(a: PnCounter, b: PnCounter): PnCounter {
  const left = normalizePnCounter(a);
  const right = normalizePnCounter(b);
  return {
    inc: mergeSiteCountMaps(left.inc, right.inc),
    dec: mergeSiteCountMaps(left.dec, right.dec),
  };
}
```

**Op application**: Adds to the site's accumulator, not max:

```typescript
// src/core/crdt/pnCounter.ts:58-74
export function applyPnCounterDelta(
  counter: PnCounter, site: string, direction: PnDirection, amount: number,
): PnCounter {
  // ...
  const next = { ...target, [site]: (target[site] ?? 0) + amount };
  // ...
}
```

**Critical distinction**: `mergePnCounter` (state merge) takes per-site max.
`applyPnCounterDelta` (op application) adds. This means counter ops are NOT
idempotent. The system relies on the replicated log's seq ordering to apply each
op exactly once. If a delta containing counter ops is replayed, the counter
inflates. The atomic state bundle (section 7.2) was introduced specifically to
prevent this scenario.

**Materialization**: `pnCounterValue = sum(inc) - sum(dec)` (`src/core/crdt/pnCounter.ts:76-81`).

### 3.3 OR-Set (tag = 3)

```typescript
// src/core/crdt/orSet.ts:3-16
export type OrSetTag = { addHlc: Hlc; addSite: string };
export type OrSetElement<T> = { val: T; tag: OrSetTag };
export type OrSet<T> = {
  elements: Array<OrSetElement<T>>;
  tombstones: OrSetTag[];
};
```

**Merge**: Union elements, union tombstones, then filter out any element whose
add-tag appears in tombstones:

```typescript
// src/core/crdt/orSet.ts:100-105
export function mergeOrSet<T>(a: OrSet<T>, b: OrSet<T>): OrSet<T> {
  return canonicalizeOrSet({
    elements: [...a.elements, ...b.elements],
    tombstones: [...a.tombstones, ...b.tombstones],
  });
}
```

`canonicalizeOrSet` (`src/core/crdt/orSet.ts:90-98`) deduplicates, sorts, and
removes tombstoned elements. The sort order uses a composite key of
`wallMs:counter:site|value_fingerprint`.

**REMOVE semantics**: The client must observe the current add-tags for the value
it wants to remove. The `resolveSetRemoveTagsFromRows` function
(`src/core/sqlEval.ts:509-527`) looks up current elements matching the value and
returns their tags. If no tags are found (the element was never observed locally),
REMOVE produces zero ops -- it is a no-op, not an error.

### 3.4 MV-Register (tag = 4)

```typescript
// src/core/crdt/mvRegister.ts:3-11
export type MvRegisterValue<T> = { val: T; hlc: Hlc; site: string };
export type MvRegister<T> = { values: Array<MvRegisterValue<T>> };
```

**Merge**: Concatenate, deduplicate by event identity `(hlc, site)`, prune
dominated values, and sort:

```typescript
// src/core/crdt/mvRegister.ts:94-100
export function canonicalizeMvRegister<T>(state: MvRegister<T>): MvRegister<T> {
  assertMvEventConsistency(state.values);
  const deduped = dedupeByEvent(state.values);
  const undominated = pruneDominatedBySameSite(deduped);
  const values = undominated.sort((left, right) => compareKeys(entrySortKey(left), entrySortKey(right)));
  return { values };
}
```

**Dominated-value pruning** (P2-2 fix): The `pruneDominatedBySameSite` function
(`src/core/crdt/mvRegister.ts:77-92`) finds the maximum HLC for each site, then
discards any value from that site with a lower HLC:

```typescript
// src/core/crdt/mvRegister.ts:77-92
function pruneDominatedBySameSite<T>(values: Array<MvRegisterValue<T>>): Array<MvRegisterValue<T>> {
  const maxBySite = new Map<string, Hlc>();
  for (const entry of values) {
    const currentMax = maxBySite.get(entry.site);
    if (!currentMax || compareHlc(entry.hlc, currentMax) > 0) {
      maxBySite.set(entry.site, entry.hlc);
    }
  }
  return values.filter((entry) => {
    const max = maxBySite.get(entry.site);
    if (!max) return true;
    return compareHlc(entry.hlc, max) === 0;
  });
}
```

This ensures only the latest value from each site survives. True conflicts --
concurrent writes from different sites -- are preserved, while superseded writes
from the same site are discarded. This bounds the register size to O(number of
concurrent sites) rather than O(total writes).

**Materialization**: If a single value, return it directly. If multiple, return
an array -- the application must resolve the conflict:

```typescript
// src/core/sqlEval.ts:377-382
case 4:
  values[column] =
    state.state.values.length === 1
      ? state.state.values[0]!.val
      : state.state.values.map((entry) => entry.val);
  break;
```

---

## 4. Timestamps and Causal Ordering

### 4.1 Hybrid Logical Clock (HLC)

The HLC is a packed 64-bit bigint:

```typescript
// src/core/hlc.ts:58-61
export function packHlc(hlc: Hlc): bigint {
  assertHlcInBounds(hlc);
  return (BigInt(hlc.wallMs) << 16n) | BigInt(hlc.counter);
}
```

- **Bits 63..16** (48 bits): wall clock milliseconds.
- **Bits 15..0** (16 bits): logical counter.

This gives 2^48 milliseconds (~8,900 years from epoch) for wall time and up to
65,535 logical events within the same millisecond.

### 4.2 Functional Clock API

The HLC module (`src/core/hlc.ts`) exposes a fully functional API, refactored
from earlier class-based designs:

```typescript
// src/core/hlc.ts:165-188
export type HlcClock = {
  driftLimitMs: number;
  nowWallMs(): number;
  next(previous: Hlc | null): Hlc;
  recv(local: Hlc | null, remote: Hlc): Hlc;
};

export function createHlcClock(options: {
  nowWallMs?: () => number;
  driftLimitMs?: number;
} = {}): HlcClock {
  const nowWallMs = options.nowWallMs ?? createMonotonicWallClock();
  const driftLimitMs = normalizeDriftLimitMs(options.driftLimitMs ?? HLC_DRIFT_LIMIT_MS);
  return {
    driftLimitMs,
    nowWallMs,
    next(previous: Hlc | null): Hlc {
      return nextMonotonicHlc(previous, nowWallMs(), driftLimitMs);
    },
    recv(local: Hlc | null, remote: Hlc): Hlc {
      return recvMonotonicHlc(local, remote, nowWallMs(), driftLimitMs);
    },
  };
}
```

The `HlcClock` object bundles the wall-clock source with drift limits, providing
two operations:
- **`next(previous)`**: Generate the next local HLC, strictly greater than
  `previous`.
- **`recv(local, remote)`**: Merge a remote HLC with the local clock state,
  advancing the local clock to max(local, remote, wall) while preserving
  monotonicity.

### 4.3 Monotonic Wall Clock Synthesis

Raw `Date.now()` is not monotonic (NTP adjustments, system suspend). The
`createMonotonicWallClock` function (`src/core/hlc.ts:135-163`) synthesizes a
monotonic source by combining `Date.now()` with `performance.now()`:

```typescript
// src/core/hlc.ts:135-163
export function createMonotonicWallClock(input: {
  dateNow?: () => number;
  performance?: MonotonicPerformance | null;
} = {}): () => number {
  // ...
  let offsetMs = normalizeMs(dateNow(), 'wall') - normalizeMs(performanceClock.now(), 'monotonic');
  let last = 0;
  return () => {
    const monotonicNow = normalizeMs(performanceClock.now(), 'monotonic');
    const wallNow = normalizeMs(dateNow(), 'wall');
    const monotonicWallNow = offsetMs + monotonicNow;
    if (wallNow > monotonicWallNow) {
      offsetMs = wallNow - monotonicNow;
    }
    last = Math.max(last, offsetMs + monotonicNow, wallNow);
    return last;
  };
}
```

The design: anchor `performance.now()` (monotonic but relative) to `Date.now()`
(absolute but potentially non-monotonic). If `Date.now()` jumps forward
(NTP correction), re-anchor. The `last` variable ensures strict monotonicity.

### 4.4 Drift Rejection

Remote HLCs are validated against a configurable drift limit (default: 60
seconds):

```typescript
// src/core/hlc.ts:77-90
export function assertHlcDrift(
  hlc: Hlc,
  nowMs: number,
  driftLimitMs: number = HLC_DRIFT_LIMIT_MS,
): void {
  const now = normalizeMs(nowMs, 'wall');
  const driftLimit = normalizeDriftLimitMs(driftLimitMs);
  assertHlcInBounds(hlc);
  if (hlc.wallMs > now + driftLimit) {
    throw new Error(
      `HLC drift violation: wall clock ${hlc.wallMs}ms exceeds local wall clock ${now}ms by more than ${driftLimit}ms`,
    );
  }
}
```

Both `nextMonotonicHlc` (line 92) and `recvMonotonicHlc` (line 110) call
`assertHlcDrift`, ensuring that a compromised or misconfigured replica cannot
push the global clock arbitrarily far into the future.

### 4.5 HLC Comparison with Site Tiebreaking

```typescript
// src/core/hlc.ts:70-75
export function compareWithSite(a: Hlc, aSite: string, b: Hlc, bSite: string): number {
  const hlcCmp = compareHlc(a, b);
  if (hlcCmp !== 0) return hlcCmp;
  if (aSite === bSite) return 0;
  return aSite > bSite ? 1 : -1;
}
```

The total order is: **(wallMs, counter, siteId)** with lexicographic site
comparison. Since site IDs are UUIDv4 hex strings (32 chars), the comparison
is deterministic across all replicas.

### 4.6 Persisted HLC Fence

The `PersistedHlcFence` class (`src/core/hlc.ts:196-219`) provides strict
monotonicity enforcement across process restarts:

```typescript
// src/core/hlc.ts:196-219
export class PersistedHlcFence {
  private highWater: Hlc | null;

  constructor(initial: Hlc | null = null) { this.highWater = initial; }

  loadPersisted(highWater: Hlc | null): void { this.highWater = highWater; }
  assertNext(candidate: Hlc): void { assertHlcStrictlyIncreases(this.highWater, candidate); }
  commit(candidate: Hlc): void { this.assertNext(candidate); this.highWater = candidate; }
  snapshot(): Hlc | null { return this.highWater; }
}
```

### 4.7 HLC Hex Encoding

Because MessagePack's integer type is signed 64-bit and cannot represent the
full HLC range unambiguously across languages, HLCs are stored as hex strings:

```typescript
// src/core/sqlEval.ts:142-152
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
```

---

## 5. Operations: From SQL to CRDT Ops

### 5.1 The EncodedCrdtOp Union

Every SQL write produces one or more `EncodedCrdtOp` values:

```typescript
// src/core/sql.ts:148-197
type BaseCrdtOp = { tbl: string; key: SqlPrimaryKey; hlc: string; site: string };

export type RowExistsOp = BaseCrdtOp & { kind: 'row_exists'; exists: boolean };
export type CellLwwOp = BaseCrdtOp & { kind: 'cell_lww'; col: string; val: SqlValue };
export type CellCounterOp = BaseCrdtOp & { kind: 'cell_counter'; col: string; d: 'inc'|'dec'; n: number };
export type CellOrSetAddOp = BaseCrdtOp & { kind: 'cell_or_set_add'; col: string; val: SqlValue };
export type CellOrSetRemoveOp = BaseCrdtOp & { kind: 'cell_or_set_remove'; col: string; tags: SetRemoveTag[] };
export type CellMvRegisterOp = BaseCrdtOp & { kind: 'cell_mv_register'; col: string; val: SqlValue };
```

Every op carries the full routing key: `(tbl, key, col, hlc, site)`. This is
crucial for the merge to work without requiring any schema lookup -- the op is
self-describing.

### 5.2 SQL-to-Ops Compilation

The `generateCrdtOps` function (`src/core/sql.ts:1534-1563`) dispatches by
statement kind. Every write statement first emits a `row_exists` op, then
per-column ops:

| SQL Statement | Emitted Ops |
|---|---|
| `INSERT INTO t (pk, c1, c2) VALUES (...)` | `row_exists(true)`, then per-column: `cell_lww` / `cell_counter` / `cell_or_set_add` / `cell_mv_register` |
| `UPDATE t SET c1 = v WHERE pk = k` | `row_exists(true)`, then per-assignment: `cell_lww` / `cell_mv_register` |
| `INC t.c BY n WHERE pk = k` | `row_exists(true)`, `cell_counter(d='inc', n)` |
| `DEC t.c BY n WHERE pk = k` | `row_exists(true)`, `cell_counter(d='dec', n)` |
| `ADD v TO t.c WHERE pk = k` | `row_exists(true)`, `cell_or_set_add(val=v)` |
| `REMOVE v FROM t.c WHERE pk = k` | If tags found: `row_exists(true)`, `cell_or_set_remove(tags=...)`. If no tags: zero ops (no-op). |
| `DELETE FROM t WHERE pk = k` | `row_exists(false)` only |
| `CREATE TABLE t (...)` | LWW ops against `information_schema.tables` and `information_schema.columns` |
| `ALTER TABLE t ADD COLUMN c TYPE` | LWW ops against `information_schema.columns` |

**Each column op gets a fresh HLC** via `context.nextHlc()`. So an INSERT
touching 5 columns produces 6 HLC ticks (one for row_exists, five for columns).
This ensures every cell write has a unique timestamp.

### 5.3 INSERT is Upsert

INSERT does NOT check for row existence. The CRDT merge handles it:
- LWW: latest timestamp wins, so a second INSERT just overwrites if newer.
- Counter: accumulates.
- OR-Set: adds a new element.
This is a deliberate design choice. No INSERT-or-error behavior exists.

### 5.4 UPDATE Cannot Target Counters or Sets

The SQL compiler rejects `UPDATE tasks SET points = 5 WHERE ...` if `points` is
a counter (`src/core/sql.ts:1392`). You must use `INC`/`DEC`. Similarly, sets
require `ADD`/`REMOVE`. This prevents accidentally generating a non-CRDT
read-modify-write.

### 5.5 Information Schema Write Protection

Direct user writes to information schema tables are blocked:

```typescript
// src/core/sql.ts:1100-1109
function isInformationSchemaTable(table: string): boolean {
  return table.startsWith('information_schema.');
}

function assertUserTableWrite(table: string, statementKind: SqlStatement['kind']): void {
  if (isInformationSchemaTable(table)) {
    throw new Error(
      `${statementKind.toUpperCase()} cannot target '${table}'; information_schema is append-only metadata`,
    );
  }
}
```

Only the schema mutation planner (`planCreateTableSchemaMutation`,
`planAlterAddColumnSchemaMutation`) can generate ops targeting the information
schema. This ensures schema integrity while allowing the metadata to replicate
as normal CRDT state.

---

## 6. Op Application and State Merging

### 6.1 Applying Ops to In-Memory State

The central function `applyCrdtOpToRows` (`src/core/sqlEval.ts:529-654`) applies
a single op to the in-memory row map. It:

1. Looks up the row by `rowStorageKey(op.tbl, op.key)`, creating one if absent.
2. Decodes `op.hlc` from hex string to `Hlc`.
3. Dispatches on `op.kind`:
   - `row_exists` -> merges an LWW register on the `_exists` column.
   - `cell_lww` -> merges an LWW register on the named column.
   - `cell_counter` -> applies a PN-counter delta (adds, not max).
   - `cell_or_set_add` -> merges a singleton OR-Set.
   - `cell_or_set_remove` -> merges tombstones into the OR-Set.
   - `cell_mv_register` -> merges a singleton MV-Register.
4. Type checks: if a column already has a different `typ`, it throws. This
   prevents type confusion from corrupt ops.

### 6.2 Materialization

`materializeRow` converts CRDT state to plain JavaScript values for query
results:

| CRDT Type | Materialized As |
|---|---|
| LWW Register | The value directly |
| PN-Counter | `sum(inc) - sum(dec)` as a number |
| OR-Set | Array of distinct values (deduped by JSON fingerprint) |
| MV-Register | Single value if length 1; array of values if conflict |

The `_exists` column is skipped during materialization.

---

## 7. Physical Storage

### 7.1 MessagePack Everywhere

All binary files use MessagePack encoding via `@msgpack/msgpack`:

```typescript
// src/core/encoding.ts:1-9
import { decode, encode } from '@msgpack/msgpack';

export function encodeBin(value: unknown): Uint8Array {
  return encode(value);
}
export function decodeBin<T>(bytes: Uint8Array): T {
  return decode(bytes) as T;
}
```

**Design tradeoff**: ~10-20% size overhead vs a custom binary format, but every
file is dumpable as JSON for debugging.

### 7.2 Node Client Atomic State Bundle

The `NodeCrdtClient` (`src/platform/node/nodeClient.ts`) uses an atomic state
bundle for crash-safe persistence:

```typescript
// src/platform/node/nodeClient.ts:56-61
type AtomicStateBundleFile = {
  v: 1;
  state: StateFile;
  pending: PendingFile;
  sync: SyncFileV2;
};
```

All state is committed in a single atomic write:

```typescript
// src/platform/node/nodeClient.ts:310-351
private async persistStateFiles(): Promise<void> {
  const stateFile: StateFile = { v: 1, rows: runtimeRowsToEval(this.rows), lastLocalHlc: ... };
  const pendingFile: PendingFile = { v: 1, pendingOps: this.pendingOps };
  const syncFile: SyncFileV2 = { v: 2, syncedBySite: ... };

  const atomicBundle: AtomicStateBundleFile = {
    v: 1,
    state: stateFile,
    pending: pendingFile,
    sync: syncFile,
  };

  // Commit the authoritative local state as one atomically-renamed bundle.
  await this.writeFileAtomically(this.atomicStateBundlePath, encodeBin(atomicBundle));

  // Legacy split files remain for backwards compatibility and tooling.
  await Promise.all([
    this.writeFileAtomically(this.schemaPath, encodeBin(this.schema)),
    this.writeFileAtomically(this.statePath, encodeBin(stateFile)),
    this.writeFileAtomically(this.pendingPath, encodeBin(pendingFile)),
    this.writeFileAtomically(this.syncPath, encodeBin(syncFile)),
  ]);
}
```

The `writeFileAtomically` method uses the temp-file + rename pattern:

```typescript
// src/platform/node/nodeClient.ts:367-377
private async writeFileAtomically(path: string, bytes: Uint8Array): Promise<void> {
  const tempPath = `${path}.tmp-${process.pid}-${Date.now()}-${Math.random().toString(16).slice(2)}`;
  await mkdir(dirname(path), { recursive: true });
  await writeFile(tempPath, bytes);
  try {
    await rename(tempPath, path);
  } catch (error) {
    await rm(tempPath, { force: true });
    throw error;
  }
}
```

On POSIX systems, `rename(2)` is atomic: the target file is either the old
version or the new version, never a partial write. The unique temp path
(`pid + timestamp + random`) prevents collisions between concurrent processes.

**Why this matters**: Before this fix (P0-1/P0-2), the three files
(`state.bin`, `pending.bin`, `sync.bin`) were written with `Promise.all`. A
crash between writes could leave `state.bin` updated but `sync.bin` stale,
causing PN-counter ops to be replayed on restart and silently inflating counter
values. The atomic bundle ensures all three pieces of state are consistent:
either the entire new state is visible, or the entire old state is.

On startup, the client prefers the atomic bundle over legacy split files:

```typescript
// src/platform/node/nodeClient.ts:272-274
const state = atomicBundle?.state ?? legacyState;
const pending = atomicBundle?.pending ?? legacyPending;
const sync = atomicBundle?.sync ?? legacySync;
```

Local files layout:

| File | Type | Contents |
|---|---|---|
| `state_bundle.bin` | MessagePack `AtomicStateBundleFile` | All state, pending ops, sync cursors (authoritative) |
| `schema.bin` | MessagePack `SqlSchema` | Table definitions (also materialized from info schema rows) |
| `state.bin` | MessagePack `StateFile` | All row CRDT state + last local HLC (legacy) |
| `pending.bin` | MessagePack `PendingFile` | Ops not yet pushed to replicated log (legacy) |
| `sync.bin` | MessagePack `SyncFileV2` | Per-site sync cursor (legacy) |

### 7.3 Sync Cursor Persistence

The sync file tracks how far each site has been replicated:

```typescript
// src/platform/node/nodeClient.ts:40-49
type SyncFileV2 = {
  v: 2;
  syncedBySite: Record<string, {
    seq: LogPosition;
    hlc: string | null;
  }>;
};
```

The `hlc` field was added to detect log rewrites. During `pull()`, the client
re-reads the entry at the cursor position and compares its HLC against the
stored one. A mismatch indicates the remote log was reset or rewritten:

```typescript
// src/platform/node/nodeClient.ts:191-196
const expectedHlc = this.syncedHlcBySite.get(siteId);
if (expectedHlc !== undefined && atCursor.hlc !== expectedHlc) {
  throw new Error(
    `sync cursor mismatch for site '${siteId}' at seq ${since}; ...`
  );
}
```

---

## 8. Browser Client

The `BrowserCrdtClient` (`src/platform/browser/browserClient.ts`) is a lighter
variant of the Node client, optimized for in-browser use:

- **In-memory state**: Row state, pending ops, and sync cursors are held in
  memory only. A page refresh loses them.
- **HLC persistence via localStorage** (P1-1 fix): The local HLC high-water
  mark IS persisted, preventing clock regression across page reloads.
- **Snapshot store integration**: Supports segment hydration from the
  `SnapshotStore` interface, identical to the Node client.

### 8.1 HLC Persistence

```typescript
// src/platform/browser/browserClient.ts:31-34
export type BrowserHlcStorage = {
  getItem(key: string): string | null;
  setItem(key: string, value: string): void;
};
```

The storage is keyed per site ID:

```typescript
// src/platform/browser/browserClient.ts:36-37
const BROWSER_HLC_KEY_PREFIX = 'crdtbase.browser.hlc.';
```

At construction time, the client resolves localStorage (or a provided override):

```typescript
// src/platform/browser/browserClient.ts:38-45
function resolveDefaultBrowserHlcStorage(): BrowserHlcStorage | null {
  try {
    const storage = (globalThis as { localStorage?: BrowserHlcStorage }).localStorage;
    return storage ?? null;
  } catch {
    return null;
  }
}
```

Every local HLC tick persists immediately:

```typescript
// src/platform/browser/browserClient.ts:194-199
private nextLocalHlcHex(): string {
  const next = this.hlcClock.next(this.lastLocalHlc);
  this.lastLocalHlc = next;
  const encoded = encodeHlcHex(next);
  this.persistLocalHlc(encoded);
  return encoded;
}
```

And on `open()`, the persisted value is restored:

```typescript
// src/platform/browser/browserClient.ts:256-265
private loadPersistedLocalHlc(): void {
  if (!this.storage) return;
  const encoded = this.storage.getItem(this.hlcStorageKey);
  if (!encoded) return;
  this.lastLocalHlc = decodeHlcHex(encoded);
}
```

This prevents the critical scenario where a page refresh within the same
millisecond could reuse an `(wallMs, counter)` pair, violating the HLC strict
monotonicity invariant and potentially producing conflicting events that cause
`assertLwwEventConsistency` to throw on other replicas.

### 8.2 Snapshot Coverage Gate

Both Node and Browser clients implement the `manifestCoversKnownSites` check:

```typescript
// src/platform/browser/browserClient.ts:321-330
private manifestCoversKnownSites(manifest: ManifestFile): boolean {
  for (const [siteId, seq] of this.syncedSeqBySite.entries()) {
    if (seq <= 0) continue;
    if (!(siteId in manifest.sites_compacted)) return false;
  }
  return true;
}
```

This is called before applying a new snapshot manifest. If the manifest does not
include compaction watermarks for all sites the client has previously synced
with, the manifest is rejected. Without this gate, switching to a partial
snapshot could cause rows to be dropped and required log replay to be skipped.

---

## 9. Replicated Log

### 9.1 The Interface

```typescript
// src/core/replication.ts:1-19
export type LogPosition = number;

export type LogEntry = {
  siteId: string;
  hlc: string;       // hex-encoded bigint, latest HLC in this batch
  seq: LogPosition;   // per-site sequence number
  ops: EncodedCrdtOp[];
};

export interface ReplicatedLog {
  append(entry: AppendLogEntry): Promise<LogPosition>;
  readSince(siteId: string, since: LogPosition): Promise<LogEntry[]>;
  listSites(): Promise<string[]>;
  getHead(siteId: string): Promise<LogPosition>;
}
```

**Key invariant**: `seq` is monotonically increasing per site. `append()`
assigns the next seq. `readSince()` returns entries with `seq > since`.

### 9.2 Contiguous Prefix Safety

The `takeContiguousEntriesSince` function (`src/core/replication.ts:28-46`)
protects against cursor skips under eventually consistent storage (S3):

```typescript
// src/core/replication.ts:28-46
export function takeContiguousEntriesSince(
  entries: readonly LogEntry[], since: LogPosition,
): LogEntry[] {
  const ordered = [...entries].sort((left, right) => left.seq - right.seq);
  const contiguous: LogEntry[] = [];
  let expected = since + 1;
  for (const entry of ordered) {
    if (entry.seq < expected) continue;
    if (entry.seq !== expected) break;  // gap detected, stop here
    contiguous.push(entry);
    expected += 1;
  }
  return contiguous;
}
```

If the listing returns seqs `[3, 5]` (missing 4), only seq 3 is returned. This
prevents the cursor from advancing past a gap, which would permanently skip ops.

### 9.3 HTTP Server Implementation

The `FileReplicatedLogServer` (`src/backend/fileLogServer.ts`) stores log entries
as individual files on the filesystem:

```
{rootDir}/logs/{siteId}/{seq:010}.bin    -- one MessagePack LogEntry per file
{rootDir}/snapshots/manifest.bin         -- manifest
{rootDir}/snapshots/schema.bin           -- schema
{rootDir}/snapshots/{segments}/...       -- segment files
```

### 9.4 S3 Implementation

The `S3ReplicatedLog` (`src/backend/s3ReplicatedLog.ts`) maps the log interface
onto S3 objects:

```
deltas/{siteId}/{seq:010}.delta.bin
```

Append uses `IfNoneMatch: '*'` for optimistic concurrency -- if the object
already exists (another process appended first), it retries up to 5 times.

---

## 10. Snapshot Store and Compaction

### 10.1 The SnapshotStore Interface

```typescript
// src/core/snapshotStore.ts:7-14
export interface SnapshotStore {
  getManifest(): Promise<ManifestFile | null>;
  putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean>;
  getSegment(path: string): Promise<Uint8Array | null>;
  putSegment(path: string, data: Uint8Array): Promise<void>;
  getSchema(): Promise<SqlSchema | null>;
  putSchema(schema: SqlSchema): Promise<void>;
}
```

`putManifest` is the single coordination point: compare-and-set using
`expectedVersion`. If the current manifest version does not match, the write
fails.

### 10.2 Segment Files

A segment contains the merged CRDT state for a set of rows in one table
partition:

```typescript
// src/core/compaction.ts:19-28
export type SegmentFile = {
  v: 1;
  table: string;
  partition: string;
  hlc_max: string;
  row_count: number;
  bloom: Uint8Array;
  bloom_k: number;
  rows: SegmentRow[];
};
```

Rows are sorted by primary key. The bloom filter enables fast point lookups:

```typescript
// src/core/compaction.ts:199-225
export function buildBloomFilter(
  keys: SqlPrimaryKey[], bitsPerElement = 10,
): { bloom: Uint8Array; bloomK: number } {
  // FNV-1a hash, multiple seeds for k hash functions
  // Target: 1% false positive rate
}
```

**File naming**: `segments/{table}_{partition}_{hlcMax8}.seg.bin`

### 10.3 Manifest File

```typescript
// src/core/compaction.ts:41-47
export type ManifestFile = {
  v: 1;
  version: number;                        // monotonic, incremented on compaction
  compaction_hlc: string;                 // all ops <= this HLC are in segments
  segments: ManifestSegmentRef[];
  sites_compacted: Record<string, number>; // siteId -> last compacted seq
};
```

### 10.4 Compaction Retention Policy

Compaction now applies a configurable retention policy to prune expired
tombstones:

```typescript
// src/core/compaction.ts:54-61
export const DEFAULT_OR_SET_TOMBSTONE_TTL_MS = 7 * 24 * 60 * 60 * 1000;
export const DEFAULT_ROW_TOMBSTONE_TTL_MS = 7 * 24 * 60 * 60 * 1000;

export type CompactionRetentionPolicy = {
  nowMs: number;
  orSetTombstoneTtlMs: number;
  rowTombstoneTtlMs: number;
};
```

The `pruneRuntimeRowsForCompaction` function (`src/core/compaction.ts:423-464`)
applies two pruning passes:

**Row tombstone pruning**: If a row's `_exists` LWW register is `false` and its
HLC wall clock is older than the row tombstone cutoff, the entire row is deleted
from the in-memory map:

```typescript
// src/core/compaction.ts:434-443
const exists = row.columns.get('_exists');
if (
  exists?.typ === 1 &&
  exists.state.val === false &&
  isHlcExpired(exists.state.hlc.wallMs, rowCutoffMs)
) {
  rows.delete(storageKey);
  continue;
}
```

**OR-Set tombstone pruning**: For each OR-Set column, tombstones whose HLC is
older than the OR-Set tombstone cutoff are filtered out, and the set is
re-canonicalized:

```typescript
// src/core/compaction.ts:445-463
for (const [column, state] of row.columns.entries()) {
  if (state.typ !== 3) continue;
  const retainedTombstones = state.state.tombstones.filter(
    (tag) => !isHlcExpired(tag.addHlc.wallMs, orSetCutoffMs),
  );
  if (retainedTombstones.length === state.state.tombstones.length) continue;
  row.columns.set(column, {
    typ: 3,
    state: canonicalizeOrSet({
      elements: state.state.elements,
      tombstones: retainedTombstones,
    }),
  });
}
```

**Default TTL**: 7 days for both OR-Set tombstones and row tombstones. This
balances storage growth against the risk that a long-offline replica might miss
a tombstone and re-introduce a deleted element. A 7-day window is chosen to
cover typical offline periods.

### 10.5 Compaction Process

The compactor (`src/platform/node/compactor.ts`):

1. Reads the current manifest (or creates an empty one).
2. Loads all existing segment files into a merged in-memory row map.
3. For each site, reads log entries since the last compacted seq.
4. Applies all new ops to the merged row map.
5. Applies the retention policy (prune expired tombstones).
6. Re-partitions rows by table and partition key.
7. Builds new segment files (sorted rows, bloom filter, hlc_max).
8. Writes segments to the snapshot store.
9. Builds a new manifest with `version = old + 1`.
10. CAS-writes the manifest. If CAS fails, discards work (orphaned segments are
   harmless).

### 10.6 Client Segment Hydration

When `NodeCrdtClient.pull()` or `BrowserCrdtClient.pull()` runs, it checks for
a newer manifest:

```typescript
// src/platform/node/nodeClient.ts:379-432
private async refreshFromSnapshotManifest(): Promise<void> {
  if (!this.snapshots) return;
  const manifest = await this.snapshots.getManifest();
  if (manifest === null || manifest.version <= this.localSnapshotManifestVersion) return;
  if (!this.manifestCoversKnownSites(manifest)) return;  // coverage gate

  const rows = new Map<string, RuntimeRowState>();
  // Download all segments, merge into fresh row map
  // Re-apply pending (unpushed) ops for read-your-writes
  // Reset sync cursors to compaction watermarks
}
```

The critical step is resetting sync cursors to `manifest.sites_compacted` so
that uncompacted deltas (those with seq > compacted) are replayed. Compacted
deltas are already incorporated in the segments.

---

## 11. Formal Verification in Lean

### 11.1 Table CRDT Model

The Lean formalization models a composite row CRDT:

```lean
-- lean/CrdtBase/Crdt/Table/Defs.lean:11-17
structure TableRowState (alpha beta gamma Hlc : Type) where
  alive : LwwRegister Bool
  lwwCol : LwwRegister alpha
  counterCol : PnCounter
  setCol : OrSet beta Hlc
  registerCol : MvRegister gamma
```

Table state is a function from key to row state:

```lean
-- lean/CrdtBase/Crdt/Table/Defs.lean:30
abbrev TableState (kappa alpha beta gamma Hlc : Type) := kappa -> TableRowState alpha beta gamma Hlc
```

### 11.2 Proven Properties

From `lean/CrdtBase/Crdt/Table/Props.lean`:

- **Table merge commutativity**: `mergeTable_comm_of_valid` -- table merge is
  commutative under event consistency.
- **Table merge associativity**: `mergeTable_assoc_of_valid` -- table merge is
  associative under event consistency.
- **Table merge idempotence**: `mergeTable_idem_of_valid` -- table merge is
  idempotent under event consistency.
- **Row-level semilattice**: `mergeTableRow_comm_of_valid`,
  `mergeTableRow_assoc_of_valid`, `mergeTableRow_idem_of_valid` -- proven
  directly under `ValidTableRowPair`/`Triple` predicates (P1-2 fix).
- **Visibility preservation**: Counter, set, and register updates do not change
  row visibility (`apply_counter_preserves_visibility`,
  `apply_set_preserves_visibility`, `apply_register_preserves_visibility`).
- **Cross-column commutativity**: Row-existence updates commute with counter
  updates, set updates. Counter and register updates commute.
- **Disjoint-key commutativity**: Updates at different keys commute at the
  whole-table level (`modify_row_at_disjoint_commute`).

### 11.3 OR-Set Idempotence Chain

From `lean/CrdtBase/Crdt/OrSet/Props.lean` (P1-3 fix):

- **`or_set_merge_canonicalized`**: Merge output is always in canonical form.
- **`or_set_merge_idem_general`**: Composed precondition-free idempotence
  from canonicalization.

### 11.4 Convergence Framework

```lean
-- lean/CrdtBase/Convergence/Defs.lean:10-16
def applyOps {sigma alpha : Type} (step : sigma -> alpha -> sigma) (init : sigma) (ops : List alpha) : sigma :=
  List.foldl step init ops

structure SameOps {alpha : Type} (ops1 ops2 : List alpha) : Prop where
  perm : List.Perm ops1 ops2
```

This sets up the framework for proving strong eventual consistency: if two
replicas receive the same set of operations (in any order), they converge to the
same state.

### 11.5 SQL Compilation Verification

The Lean oracle (`lean/CrdtBase/Sql/Defs.lean`) independently implements
`generateCrdtOps` and `buildSelectPlan`. Differential random testing (DRT)
compares the Lean oracle's output against the TypeScript implementation. The
Lean version validates:

- Generated ops have valid type tags (1-4).
- Generated ops are "syncable" (all required fields non-empty).
- REMOVE with zero observed tags produces zero ops.

---

## 12. Correctness Analysis

### 12.1 What Makes the Model Correct

1. **Total order on events**: `(hlc, site)` provides a total order on all write
   events across all replicas. LWW merge uses this order deterministically.

2. **Column independence**: Each column has its own CRDT state. Updates to
   different columns on the same row commute because they operate on independent
   state. This is proven in Lean for the Table CRDT model.

3. **Row independence**: Updates to different rows are fully independent
   (disjoint-key commutativity, proven in Lean).

4. **Idempotent state merge**: LWW, OR-Set, and MV-Register merges are
   idempotent (merging the same state twice produces the same result). PN-Counter
   merge is also idempotent (per-site max is idempotent).

5. **Seq-based deduplication for counter ops**: Counter ops are NOT idempotent
   at the op level (`applyPnCounterDelta` adds). The system prevents double
   application by tracking per-site seq cursors and advancing them only on
   contiguous entries.

6. **Atomic local persistence**: The atomic state bundle ensures that counter
   state, pending ops, and sync cursors are always consistent after a crash.

7. **CAS on manifest**: The single point of coordination. Compaction is
   optimistic: compute new state, try to CAS the manifest. If another compaction
   ran concurrently, lose and retry.

8. **Schema as CRDT state**: Schema metadata flows through the same replication
   pipeline as data, ensuring all replicas converge to the same schema without
   requiring separate coordination.

9. **Snapshot coverage gate**: Clients reject manifests that do not cover all
   known sites, preventing partial snapshots from causing data loss.

### 12.2 P0 Issues (All FIXED)

**P0-1: PN-Counter double-application on crash recovery** -- FIXED. The
`NodeCrdtClient` now commits all local state via an atomic `state_bundle.bin`
write (temp-file + `rename`). Startup prefers the atomic bundle over legacy
split files. Counter ops can no longer be replayed due to stale sync cursors.

**P0-2: Non-atomic local persistence** -- FIXED. The `writeFileAtomically`
method uses the temp-file + `rename(2)` pattern, which is atomic on POSIX
filesystems. The atomic bundle ensures cross-file consistency.

**P0-3: FsSnapshotStore CAS not truly atomic** -- FIXED. `FsSnapshotStore.putManifest`
now uses a filesystem lock (`manifest.bin.lock`) to serialize concurrent CAS
writers, and manifest writes use temp-file + atomic `rename`.

### 12.3 P1 Issues (All FIXED)

**P1-1: Browser client does not persist HLC high-water mark** -- FIXED.
`BrowserCrdtClient` now persists a per-site local HLC high-water mark via
`localStorage` (overridable via `BrowserCrdtClientOptions.storage`), restoring
it at `open()` time.

**P1-2: Composite row semilattice not directly proved** -- FIXED. Added
`ValidTableRowPair`/`Triple` predicates and proved `mergeTableRow_comm_of_valid`,
`mergeTableRow_assoc_of_valid`, `mergeTableRow_idem_of_valid` directly under
event-consistency, then lifted to whole-table theorems.

**P1-3: OR-Set idempotence precondition not formally chained** -- FIXED. Added
`or_set_merge_canonicalized` and composed it into `or_set_merge_idem_general`
for precondition-free idempotence.

### 12.4 P2 Issues (4/8 FIXED)

| ID | Issue | Status |
|---|---|---|
| P2-1 | OR-Set tombstone growth unbounded | FIXED: TTL-based pruning (7d default) |
| P2-2 | MV-Register never prunes dominated values | FIXED: `pruneDominatedBySameSite` in canonicalize |
| P2-3 | Row-level tombstone TTL not implemented | FIXED: Same retention policy path |
| P2-4 | TS/Lean equivalence only bridged by testing | MITIGATED: DRT expanded and unified |
| P2-5 | Network layer not formally modeled | Open |
| P2-6 | HLC real-time accuracy not modeled | FIXED: Runtime guardrails (drift rejection, monotonic wall clock) |
| P2-7 | No orphaned segment cleanup | Open |
| P2-8 | No old delta file cleanup | Open |

### 12.5 Remaining Gaps

1. **Network layer assumptions**: Convergence proofs assume eventual delivery.
   S3 durability (99.999999999%) provides practical assurance but is not
   formally modeled.

2. **Orphaned segments**: Failed CAS-on-manifest leaves unreferenced segments
   in storage. No garbage collector exists.

3. **Old delta files**: After compaction folds deltas into segments, the delta
   files remain in storage indefinitely.

4. **Browser state volatility**: All row state, pending ops, and sync cursors
   are lost on page refresh. Only the HLC is persisted.

---

## 13. Summary of Data Flow

```
User SQL Statement
       |
       v
  parseSql() -> SqlStatement AST
       |
       v
  buildClientSqlExecutionPlanFromStatement()
       |
       +-- CREATE TABLE -> planCreateTableSchemaMutation()
       |     |              -> LWW ops against information_schema.tables/columns
       |     v
       |   EncodedCrdtOp[] -> standard write path
       |
       +-- ALTER TABLE ADD COLUMN -> planAlterAddColumnSchemaMutation()
       |     |                       -> LWW ops against information_schema.columns
       |     v
       |   EncodedCrdtOp[] -> standard write path
       |
       +-- SELECT -> buildSelectPlan() -> runSelectPlan() -> materialized rows
       |
       +-- Write (INSERT/UPDATE/INC/DEC/ADD/REMOVE/DELETE)
                         |
                         v
                  generateCrdtOps() -> EncodedCrdtOp[]
                         |
                         v
                  applyCrdtOpToRows() -> in-memory RuntimeRowState update
                         |
                         v
                  pendingOps buffer
                         |
                         v (on persistStateFiles)
                  state_bundle.bin (atomic temp + rename)
                         |
                         v (on push)
                  ReplicatedLog.append() -> LogEntry with seq
                         |
                         v (on pull by other replicas)
                  readSince() -> applyCrdtOpToRows() -> convergent state
                         |
                         v (refreshSchemaFromRows)
                  materializeSchemaFromRows() -> SqlSchema update
                         |
                         v (on compaction)
                  pruneRuntimeRowsForCompaction() -> TTL-based tombstone pruning
                         |
                         v
                  buildSegmentsFromRows() -> SegmentFile (MessagePack)
                         |
                         v
                  putSegment() + putManifest(CAS) -> SnapshotStore
```

The design cleanly separates concerns: SQL compilation produces CRDT ops, which
are self-describing and schema-independent. Schema metadata itself is stored as
CRDT state in the information schema tables, so it replicates through the same
pipeline as data. The ops flow through an append-only log. Compaction is a
background process that merges ops into sorted segment files with TTL-based
tombstone pruning, without affecting the live read/write path. Clients can always
read locally (offline-first) and sync when connectivity permits. Both Node and
Browser clients enforce HLC monotonicity across restarts and reject partial
snapshot manifests to preserve data integrity.
