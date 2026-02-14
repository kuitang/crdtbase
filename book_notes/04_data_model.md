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
// src/core/sql.ts:192-200
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

### 1.2 DDL: CREATE TABLE

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

The parser (`src/core/sql.ts:408-423`) converts `PRIMARY KEY` to the internal
`{ kind: 'scalar', scalar: 'STRING' }` representation. Bare scalar types on
non-PK columns are disallowed -- you must use `LWW<T>`, `COUNTER`, `SET<T>`, or
`REGISTER<T>`.

The function `tableSchemaFromCreate` (`src/core/sql.ts:882-910`) converts the
parsed AST into the runtime `SqlTableSchema`:

```typescript
// src/core/sql.ts:882-910
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

**Design decision**: Non-PK scalar columns silently become LWW. The spec
originally considered disallowing bare scalars entirely, but the code promotes
them. This means the schema is self-consistent: every non-PK column is always a
proper CRDT type internally, even if declared bare.

### 1.3 Schema Evolution

From `SPEC.md`: "Schema migrations" is listed as a non-goal. The only mutation
is `DROP TABLE`, which removes the table from the schema. Segment and delta files
for dropped tables are never cleaned up; compaction simply ignores them. There is
no ALTER TABLE.

---

## 2. Row and Column Representation

### 2.1 Runtime Row State

The in-memory representation during query execution lives in `src/core/sqlEval.ts`:

```typescript
// src/core/sqlEval.ts:26-36
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
// src/core/sqlEval.ts:132-134
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
// src/core/sqlEval.ts:420-437
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
// src/core/sqlEval.ts:549-552
const exists = row.columns.get('_exists');
if (exists && exists.typ === 1 && exists.state.val === false) {
  continue;
}
```

### 2.3 Serialized Row State (Eval Format)

For persistence and serialization, there is a parallel "eval" format that uses
hex-encoded HLC strings rather than structured `Hlc` objects:

```typescript
// src/core/sqlEval.ts:43-65
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
(`src/core/sqlEval.ts:228-311`) bridge the two representations. The eval format
is what gets encoded to MessagePack for persistence.

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
inflates.

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
(`src/core/sqlEval.ts:388-406`) looks up current elements matching the value and
returns their tags. If no tags are found (the element was never observed locally),
REMOVE produces zero ops -- it is a no-op, not an error.

### 3.4 MV-Register (tag = 4)

```typescript
// src/core/crdt/mvRegister.ts:3-11
export type MvRegisterValue<T> = { val: T; hlc: Hlc; site: string };
export type MvRegister<T> = { values: Array<MvRegisterValue<T>> };
```

**Merge**: Concatenate, deduplicate by event identity `(hlc, site)`, sort:

```typescript
// src/core/crdt/mvRegister.ts:84-88
export function mergeMvRegister<T>(a: MvRegister<T>, b: MvRegister<T>): MvRegister<T> {
  return canonicalizeMvRegister({ values: [...a.values, ...b.values] });
}
```

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

**Note on pruning**: The spec mentions "discard any where another value has
strictly higher HLC from the same site." However, the actual implementation
(`canonicalizeMvRegister`) simply keeps ALL values after deduplication. It does
not prune dominated values. This means the MV-Register only grows; concurrent
writes accumulate forever. This is technically correct (keeping extra values
never loses information), but it means the register can grow unboundedly if many
concurrent writes happen from different sites.

---

## 4. Timestamps and Causal Ordering

### 4.1 Hybrid Logical Clock (HLC)

The HLC is a packed 64-bit bigint:

```typescript
// src/core/hlc.ts:14-19
export function packHlc(hlc: Hlc): bigint {
  if (hlc.wallMs >= WALL_MS_MAX || hlc.counter >= COUNTER_MAX) {
    throw new Error('HLC out of bounds');
  }
  return (BigInt(hlc.wallMs) << 16n) | BigInt(hlc.counter);
}
```

- **Bits 63..16** (48 bits): wall clock milliseconds.
- **Bits 15..0** (16 bits): logical counter.

This gives 2^48 milliseconds (~8,900 years from epoch) for wall time and up to
65,535 logical events within the same millisecond.

### 4.2 HLC Comparison with Site Tiebreaking

```typescript
// src/core/hlc.ts:28-33
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

### 4.3 HLC Monotonicity Enforcement

The `PersistedHlcFence` class (`src/core/hlc.ts:41-64`) enforces that each new
local HLC is strictly greater than the previous. Both `NodeCrdtClient` and
`BrowserCrdtClient` use `nextMonotonicHlc`:

```typescript
// src/platform/node/nodeClient.ts:54-61
function nextMonotonicHlc(previous: Hlc | null, nowMs: number): Hlc {
  const wallMs = previous === null ? nowMs : Math.max(nowMs, previous.wallMs);
  const counter = previous !== null && wallMs === previous.wallMs ? previous.counter + 1 : 0;
  if (wallMs >= HLC_LIMITS.wallMsMax || counter >= HLC_LIMITS.counterMax) {
    throw new Error('unable to allocate monotonic HLC within bounds');
  }
  return { wallMs, counter };
}
```

The Node client persists `lastLocalHlc` to disk in `state.bin`, so it survives
restarts. The browser client does NOT persist it (it is in-memory only), which
means a page refresh could regress the counter if writes happen within the same
millisecond -- a potential correctness gap noted in the spec.

### 4.4 HLC Hex Encoding

Because MessagePack's integer type is signed 64-bit and cannot represent the
full HLC range unambiguously across languages, HLCs are stored as hex strings:

```typescript
// src/core/sqlEval.ts:136-146
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
// src/core/sql.ts:141-190
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

The `generateCrdtOps` function (`src/core/sql.ts:1225-1253`) dispatches by
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
a counter (`src/core/sql.ts:1083`). You must use `INC`/`DEC`. Similarly, sets
require `ADD`/`REMOVE`. This prevents accidentally generating a non-CRDT
read-modify-write.

---

## 6. Op Application and State Merging

### 6.1 Applying Ops to In-Memory State

The central function `applyCrdtOpToRows` (`src/core/sqlEval.ts:408-533`) applies
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

`materializeRow` (`src/core/sqlEval.ts:351-386`) converts CRDT state to plain
JavaScript values for query results:

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

### 7.2 Node Client Local Files

The `NodeCrdtClient` (`src/platform/node/nodeClient.ts`) persists four files in
its `dataDir`:

| File | Type | Contents |
|---|---|---|
| `schema.bin` | MessagePack `SqlSchema` | Table definitions |
| `state.bin` | MessagePack `StateFile` | All row CRDT state + last local HLC |
| `pending.bin` | MessagePack `PendingFile` | Ops not yet pushed to replicated log |
| `sync.bin` | MessagePack `SyncFileV2` | Per-site sync cursor (`seq` + `hlc`) |

The state file format:

```typescript
// src/platform/node/nodeClient.ts:28-32
type StateFile = {
  v: 1;
  rows: SqlEvalRowState[];
  lastLocalHlc: string | null;
};
```

**Every write persists immediately** -- `persistStateFiles()` is called after
every `exec()` and after every `push()`/`pull()` cycle. This writes all three
files (`state.bin`, `pending.bin`, `sync.bin`) in parallel:

```typescript
// src/platform/node/nodeClient.ts:301-331
private async persistStateFiles(): Promise<void> {
  // ...
  await Promise.all([
    writeFile(this.statePath, encodeBin(stateFile)),
    writeFile(this.pendingPath, encodeBin(pendingFile)),
    writeFile(this.syncPath, encodeBin(syncFile)),
  ]);
}
```

**Note**: There is no atomic transaction across these three files. A crash
between writing `state.bin` and `pending.bin` could leave them inconsistent.
However, since CRDT merges are idempotent (for LWW, OR-Set, MV-Register) or
append-only (for counters), the worst case is replaying a counter op, which would
inflate the counter. The spec acknowledges this as a known trade-off for the
learning project.

### 7.3 Sync Cursor Persistence

The sync file tracks how far each site has been replicated:

```typescript
// src/platform/node/nodeClient.ts:38-47
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
// src/platform/node/nodeClient.ts:201-206
const expectedHlc = this.syncedHlcBySite.get(siteId);
if (expectedHlc !== undefined && atCursor.hlc !== expectedHlc) {
  throw new Error(
    `sync cursor mismatch for site '${siteId}' at seq ${since}; ...`
  );
}
```

---

## 8. Replicated Log

### 8.1 The Interface

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

### 8.2 Contiguous Prefix Safety

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

### 8.3 HTTP Server Implementation

The `FileReplicatedLogServer` (`src/backend/fileLogServer.ts`) stores log entries
as individual files on the filesystem:

```
{rootDir}/logs/{siteId}/{seq:010}.bin    -- one MessagePack LogEntry per file
{rootDir}/snapshots/manifest.bin         -- manifest
{rootDir}/snapshots/schema.bin           -- schema
{rootDir}/snapshots/{segments}/...       -- segment files
```

**Routes**:

| Method | Path | Description |
|---|---|---|
| `POST` | `/logs/:siteId` | Append entry, assigns next seq, writes to disk |
| `GET` | `/logs/:siteId?since=N` | Read entries with seq > N |
| `GET` | `/logs` | List all site IDs |
| `GET` | `/logs/:siteId/head` | Latest seq for a site |
| `GET` | `/manifest` | Get manifest bytes (404 if none) |
| `PUT` | `/manifest?expect_version=N` | CAS-conditional manifest write (412 on mismatch) |
| `GET` | `/schema` | Get schema bytes |
| `PUT` | `/schema` | Upload schema |
| `GET` | `/segments/:path` | Get segment file |
| `PUT` | `/segments/:path` | Upload segment file |

The `append` handler (`src/backend/fileLogServer.ts:271-298`) does: read current
head from disk, compute `seq = head + 1`, write file. No locking -- concurrent
appends from the same site could race, though in practice each site is a single
process.

Request bodies for log operations are JSON (not MessagePack). Manifest and
segment bodies are raw binary (MessagePack-encoded).

### 8.4 S3 Implementation

The `S3ReplicatedLog` (`src/backend/s3ReplicatedLog.ts`) maps the log interface
onto S3 objects:

```
deltas/{siteId}/{seq:010}.delta.bin
```

Append uses `IfNoneMatch: '*'` for optimistic concurrency -- if the object
already exists (another process appended first), it retries up to 5 times:

```typescript
// src/backend/s3ReplicatedLog.ts:104-133
async append(entry: AppendLogEntry): Promise<LogPosition> {
  for (let attempt = 0; attempt < 5; attempt += 1) {
    const head = await this.getHead(entry.siteId);
    const nextSeq = head + 1;
    try {
      await this.client.send(new PutObjectCommand({
        Bucket: this.bucket,
        Key: objectKey,
        Body: encodeBin({ siteId, hlc, seq: nextSeq, ops } satisfies LogEntry),
        IfNoneMatch: '*',
      }));
      return nextSeq;
    } catch (error) {
      if (isRetryableAppendError(error)) continue;
      throw error;
    }
  }
}
```

The `TigrisReplicatedLog` (`src/backend/tigrisReplicatedLog.ts`) is a thin
wrapper that configures the S3 client with Tigris credentials:

```typescript
// src/backend/tigrisReplicatedLog.ts:12-26
export function createTigrisReplicatedLog(options: TigrisReplicatedLogOptions): S3ReplicatedLog {
  return new S3ReplicatedLog({
    bucket: options.bucket,
    prefix: options.prefix ?? 'deltas',
    clientConfig: {
      endpoint: options.endpoint,
      region: options.region ?? 'auto',
      forcePathStyle: false,
      credentials: { accessKeyId: ..., secretAccessKey: ... },
    },
  });
}
```

---

## 9. Snapshot Store and Compaction

### 9.1 The SnapshotStore Interface

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

### 9.2 Segment Files

A segment contains the merged CRDT state for a set of rows in one table
partition:

```typescript
// src/core/compaction.ts:13-27
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

export type SegmentRow = {
  key: SqlPrimaryKey;
  cols: Record<string, SqlEvalColumnState>;
};
```

Rows are sorted by primary key. The bloom filter enables fast point lookups:

```typescript
// src/core/compaction.ts:179-224
export function buildBloomFilter(
  keys: SqlPrimaryKey[], bitsPerElement = 10,
): { bloom: Uint8Array; bloomK: number } {
  // FNV-1a hash, multiple seeds for k hash functions
  // Target: 1% false positive rate
}
```

**File naming**: `segments/{table}_{partition}_{hlcMax8}.seg.bin`

```typescript
// src/core/compaction.ts:313-315
export function defaultSegmentPath(table: string, partition: string, hlcMax: string): string {
  return `segments/${sanitizePathToken(table)}_${sanitizePathToken(partition)}_${compactionHlcSuffix(hlcMax)}.seg.bin`;
}
```

### 9.3 Manifest File

```typescript
// src/core/compaction.ts:29-46
export type ManifestFile = {
  v: 1;
  version: number;                        // monotonic, incremented on compaction
  compaction_hlc: string;                 // all ops <= this HLC are in segments
  segments: ManifestSegmentRef[];
  sites_compacted: Record<string, number>; // siteId -> last compacted seq
};

export type ManifestSegmentRef = {
  path: string;
  table: string;
  partition: string;
  row_count: number;
  size_bytes: number;
  hlc_max: string;
  key_min: SqlPrimaryKey;
  key_max: SqlPrimaryKey;
};
```

### 9.4 Compaction Process

The compactor (`src/platform/node/compactor.ts:56-131`):

1. Reads the current manifest (or creates an empty one).
2. Loads all existing segment files into a merged in-memory row map.
3. For each site, reads log entries since the last compacted seq.
4. Applies all new ops to the merged row map.
5. Re-partitions rows by table and partition key.
6. Builds new segment files (sorted rows, bloom filter, hlc_max).
7. Writes segments to the snapshot store.
8. Builds a new manifest with `version = old + 1`.
9. CAS-writes the manifest. If CAS fails, discards work (orphaned segments are
   harmless).

```typescript
// src/platform/node/compactor.ts:113-114
const applied = await options.snapshots.putManifest(nextManifest, priorManifest.version);
```

### 9.5 Client Segment Hydration

When `NodeCrdtClient.pull()` runs, it checks for a newer manifest:

```typescript
// src/platform/node/nodeClient.ts:346-393
private async refreshFromSnapshotManifest(): Promise<void> {
  // ...
  const manifest = await this.snapshots.getManifest();
  if (manifest === null || manifest.version <= this.localSnapshotManifestVersion) return;
  // Download all segments, merge into fresh row map
  // Re-apply pending (unpushed) ops for read-your-writes
  // Reset sync cursors to compaction watermarks
}
```

The critical step is resetting sync cursors to `manifest.sites_compacted` so
that uncompacted deltas (those with seq > compacted) are replayed. Compacted
deltas are already incorporated in the segments.

---

## 10. The Tigris S3 Snapshot Store

The `TigrisSnapshotStore` (`src/backend/tigrisSnapshotStore.ts`) implements CAS
using S3 ETags:

```typescript
// src/backend/tigrisSnapshotStore.ts:132-175
async putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean> {
  const current = await this.readObject(manifestKey);
  // ...
  if (current === null) {
    putInput.IfNoneMatch = '*';   // object must not exist
  } else if (currentEtag !== null) {
    putInput.IfMatch = currentEtag; // object must match this ETag
  }
  try {
    await this.client.send(new PutObjectCommand(putInput));
    return true;
  } catch (error) {
    if (isCasConflictError(error)) return false;
    throw error;
  }
}
```

This provides compare-and-swap semantics even on eventually consistent S3 by
routing through Tigris's global leader (via `X-Tigris-Consistent: true` headers
as documented in the spec, though the actual header is not in the code -- the
ETag-based CAS provides the necessary serialization).

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

- **Table merge commutativity**: If row merge is commutative, table merge is
  commutative (`table_merge_comm_of_row_comm`).
- **Table merge associativity**: If row merge is associative, table merge is
  associative (`table_merge_assoc_of_row_assoc`).
- **Table merge idempotence**: If row merge is idempotent, table merge is
  idempotent (`table_merge_idem_of_row_idem`).
- **Visibility preservation**: Counter, set, and register updates do not change
  row visibility (`apply_counter_preserves_visibility`,
  `apply_set_preserves_visibility`, `apply_register_preserves_visibility`).
- **Cross-column commutativity**: Row-existence updates commute with counter
  updates, set updates. Counter and register updates commute
  (`row_exists_counter_commute`, `row_exists_set_commute`,
  `row_counter_register_commute`).
- **Disjoint-key commutativity**: Updates at different keys commute at the
  whole-table level (`modify_row_at_disjoint_commute`).

### 11.3 Convergence Framework

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

### 11.4 SQL Compilation Verification

The Lean oracle (`lean/CrdtBase/Sql/Defs.lean`) independently implements
`generateCrdtOps` and `buildSelectPlan`. Differential random testing (DRT)
compares the Lean oracle's output against the TypeScript implementation. The
Lean version validates:

- Generated ops have valid type tags (1-4).
- Generated ops are "syncable" (all required fields non-empty).
- REMOVE with zero observed tags produces zero ops.

---

## 12. Browser Client

The `BrowserCrdtClient` (`src/platform/browser/browserClient.ts`) is a simpler
variant of the Node client:

- No local file persistence (all state is in-memory).
- No snapshot store integration (no segment hydration).
- Same push/pull sync protocol via the `ReplicatedLog` interface.
- Same SQL parsing, op generation, and CRDT merge logic.

This means browser state is lost on page refresh. The spec notes OPFS
(`OpfsStorageAdapter`) as a planned but not-yet-implemented persistence layer.

---

## 13. Correctness Analysis

### 13.1 What Makes the Model Correct

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

6. **CAS on manifest**: The single point of coordination. Compaction is
   optimistic: compute new state, try to CAS the manifest. If another compaction
   ran concurrently, lose and retry.

### 13.2 Potential Gaps

1. **MV-Register never prunes**: The implementation keeps all values forever.
   The spec says to "discard any where another value has strictly higher HLC from
   the same site," but `canonicalizeMvRegister` only deduplicates by event
   identity. Over time, an MV-Register column with many concurrent writes would
   accumulate unbounded values.

2. **No atomic local persistence**: The three local files (`state.bin`,
   `pending.bin`, `sync.bin`) are written in parallel with `Promise.all`. A crash
   between writes could leave them inconsistent. The impact is bounded by CRDT
   properties (duplicate op application is safe for all types except counters).

3. **Browser client HLC persistence**: The browser client does not persist
   `lastLocalHlc`. A refresh within the same millisecond could reuse a counter
   value, violating the HLC strict monotonicity invariant.

4. **No tombstone TTL**: The spec mentions "compaction retains tombstones until a
   configurable TTL (default: 7 days), after which they are dropped." The current
   compaction code does not implement this TTL -- tombstoned rows and OR-Set
   tombstones accumulate forever.

5. **Non-atomic `putManifest` on filesystem**: `FsSnapshotStore.putManifest`
   does a read-then-write (not atomic rename). Two concurrent compactors could
   race. The spec notes this is acceptable for the learning project scope.

---

## 14. Summary of Data Flow

```
User SQL Statement
       |
       v
  parseSql() -> SqlStatement AST
       |
       v
  buildSqlExecutionPlanFromStatement()
       |
       +-- DDL -> schema mutation (in-memory + persist schema.bin)
       |
       +-- SELECT -> buildSelectPlan() -> runSelectPlan() -> materialized rows
       |
       +-- Write -> generateCrdtOps() -> EncodedCrdtOp[]
                         |
                         v
                  applyCrdtOpToRows() -> in-memory RuntimeRowState update
                         |
                         v
                  pendingOps buffer (persist to pending.bin)
                         |
                         v (on push)
                  ReplicatedLog.append() -> LogEntry with seq
                         |
                         v (on pull by other replicas)
                  readSince() -> applyCrdtOpToRows() -> convergent state
                         |
                         v (on compaction)
                  buildSegmentsFromRows() -> SegmentFile (MessagePack)
                         |
                         v
                  putSegment() + putManifest(CAS) -> SnapshotStore
```

The design cleanly separates concerns: SQL compilation produces CRDT ops, which
are self-describing and schema-independent. The ops flow through an append-only
log. Compaction is a background process that merges ops into sorted segment files
without affecting the live read/write path. Clients can always read locally
(offline-first) and sync when connectivity permits.
