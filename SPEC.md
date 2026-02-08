# CRDTBase: Minimum Specification

A CRDT-native database with pluggable replication backends, runnable on browser and Node.js from a single TypeScript codebase.

## 1. Goals and Non-Goals

**Goals:**
- Learn CRDT database internals by building from scratch
- Single TypeScript codebase running in browser (OPFS) and Node.js (filesystem)
- Two replication backends: in-memory server, Tigris S3
- Offline-first: full read/write without network
- Every binary file trivially dumpable to JSON for debugging

**Non-goals (for now):**
- Joins, foreign keys, uniqueness constraints beyond PK
- Transactions spanning multiple rows
- Schema migrations
- Sub-millisecond query performance
- Production hardening, auth, encryption

---

## 2. Project Structure

```
crdtbase/
├── src/
│   ├── core/                  # Zero platform dependencies
│   │   ├── crdt/              # CRDT type implementations
│   │   ├── hlc.ts             # Hybrid Logical Clock
│   │   ├── encoding.ts        # MessagePack wrappers, binary helpers
│   │   ├── segment.ts         # Segment file reader/writer
│   │   ├── bloom.ts           # Bloom filter
│   │   ├── manifest.ts        # Manifest parse/serialize
│   │   ├── engine.ts          # Query engine + write path
│   │   ├── sql.ts             # SQL parser (minimal subset)
│   │   └── interfaces.ts      # StorageAdapter, ReplicatedLog, SnapshotStore
│   │
│   ├── platform/
│   │   ├── browser/           # OPFS StorageAdapter
│   │   ├── node/              # fs StorageAdapter
│   │   └── shared/            # S3 protocol helpers (fetch-based, universal)
│   │
│   ├── backend/
│   │   ├── memory-log.ts      # In-memory ReplicatedLog (for testing/dev server)
│   │   ├── memory-server.ts   # HTTP server wrapping memory-log
│   │   └── tigris-log.ts      # Tigris S3 ReplicatedLog
│   │
│   ├── compact.ts             # Compaction job entry point
│   └── cli.ts                 # CLI: dump, inspect, query
│
├── test/
└── package.json
```

All code under `src/core/` imports nothing from `node:`, `window`, or any platform API. It operates exclusively on `ArrayBuffer`, `Uint8Array`, `DataView`, and the interfaces defined in `interfaces.ts`.

---

## 3. Dependencies

| Purpose | Package | Rationale |
|---------|---------|-----------|
| Binary encoding | `@msgpack/msgpack` | Self-describing, JSON-dumpable, browser+Node, ~8KB gzipped. Every file is a MessagePack document, making the entire database inspectable with a one-liner. |
| Bloom filter | `bloomfilter` (jasondavies) | 3K weekly downloads, tiny, works in browser. Serializes to/from typed arrays. |
| CLI | `commander` | Argument parsing for the CLI tool |
| S3 client | `@aws-sdk/client-s3` (Node), raw `fetch` (browser) | Tigris is S3-compatible. Browser uses presigned URLs via `fetch`. Node uses the SDK. |
| HTTP server | `Bun.serve` or `node:http` | For the in-memory dev server |
| Test | `vitest` | Fast, TypeScript-native |

**Not using external libraries for:**
- **HLC**: ~60 lines of code, the semantics are critical to understand for this project. Using a library hides the learning.
- **CRDTs** (LWW, PNCounter, ORSet): ~40 lines each, core to the project's purpose. These must be understood intimately.
- **SQL parser**: the subset is tiny (no joins, no subqueries). A hand-written recursive descent parser is ~150 lines and educational.
- **Segment file format**: MessagePack-based (see §6), trivially implemented on top of `@msgpack/msgpack`.

---

## 4. Core Interfaces

### 4.1 StorageAdapter (local persistence)

```typescript
interface StorageAdapter {
  read(path: string): Promise<Uint8Array | null>;
  write(path: string, data: Uint8Array): Promise<void>;
  delete(path: string): Promise<void>;
  list(prefix: string): Promise<string[]>;
  readRange(path: string, offset: number, length: number): Promise<Uint8Array>;
}
```

Implementations: `OpfsStorageAdapter` (browser), `FsStorageAdapter` (Node).

### 4.2 ReplicatedLog (delta shipping)

```typescript
interface ReplicatedLog {
  /** Append a batch of operations to this site's log. Returns the new position. */
  append(entry: LogEntry): Promise<LogPosition>;

  /** Read all entries from a given site since a position. */
  readSince(siteId: string, since: LogPosition): Promise<LogEntry[]>;

  /** List all site IDs that have written to this log. */
  listSites(): Promise<string[]>;

  /** Get the latest log position for a site. Returns 0n if no entries. */
  getHead(siteId: string): Promise<LogPosition>;
}

type LogPosition = bigint;

interface LogEntry {
  siteId: string;
  hlc: bigint;           // HLC timestamp (packed, see §5)
  pos: LogPosition;      // assigned by the log
  ops: CrdtOp[];         // the operations in this batch
}
```

Implementations: `MemoryReplicatedLog` (in-process), `HttpReplicatedLog` (client for memory-server), `TigrisReplicatedLog` (S3-based).

### 4.3 SnapshotStore (compacted segments)

```typescript
interface SnapshotStore {
  getManifest(): Promise<Manifest | null>;
  putManifest(manifest: Manifest, expectedVersion: number): Promise<boolean>;
  getSegment(path: string): Promise<Uint8Array | null>;
  putSegment(path: string, data: Uint8Array): Promise<void>;
}
```

The `putManifest` method performs compare-and-set: it succeeds only if the current manifest version matches `expectedVersion`. This is the single point of coordination.

Implementations: `FsSnapshotStore` (Node, uses atomic rename), `TigrisSnapshotStore` (S3, uses ETag CAS).

---

## 5. Hybrid Logical Clock

An HLC is a `bigint` packed as:

```
Bits 63..16 (48 bits): wall clock millis (good until year 10502)
Bits 15..0  (16 bits): logical counter
```

Packing/unpacking:

```
pack(wallMs, counter) → (BigInt(wallMs) << 16n) | BigInt(counter)
unpack(hlc) → { wallMs: Number(hlc >> 16n), counter: Number(hlc & 0xFFFFn) }
```

The site ID is NOT embedded in the HLC. It travels alongside it in every operation. Tiebreaking when two HLCs are identical uses lexicographic comparison of site IDs (which are random UUIDv4 hex strings, 32 chars).

**HLC rules:**
- On local event: `wallMs = max(local_hlc.wallMs, Date.now())`. If wallMs is unchanged from the last event, increment counter. Otherwise reset counter to 0.
- On receiving remote HLC: `wallMs = max(local_hlc.wallMs, remote_hlc.wallMs, Date.now())`. Counter = if all three wallMs are equal, `max(local_counter, remote_counter) + 1`, else if two tied at max, winner's `counter + 1`, else 0.
- Reject if `wallMs` drifts more than 60 seconds ahead of `Date.now()`. This bounds clock skew.

---

## 6. Binary Format: MessagePack Everywhere

**Design principle:** Every binary file in the system is a valid MessagePack document. This means any file can be inspected with:

```bash
crdtbase dump path/to/file.bin          # pretty-printed JSON
crdtbase dump path/to/file.bin --raw    # raw msgpack structure
```

No custom binary parsing needed for debugging. No hex editors. No "magic byte" headers that require bespoke tooling. The tradeoff is ~10-20% size overhead vs a hand-rolled format. For a learning project, the debuggability is worth far more.

### 6.1 Delta File

A delta file is a single MessagePack-encoded object:

```typescript
type DeltaFile = {
  v: 1;                       // format version
  site: string;               // site ID that produced this delta
  seq: number;                // monotonic sequence number within this site
  hlc_min: string;            // hex-encoded bigint, earliest HLC in this delta
  hlc_max: string;            // hex-encoded bigint, latest HLC in this delta
  ops: EncodedOp[];           // array of operations
};

type EncodedOp = {
  tbl: string;                // table name
  key: MsgpackValue;          // primary key value (string | number)
  col: string;                // column name
  typ: number;                // CRDT type tag (see §7)
  hlc: string;                // hex-encoded bigint HLC of this operation
  site: string;               // site that originated this op
  val: MsgpackValue;          // the operation payload (type-specific, see §7)
};
```

HLCs are hex strings (e.g., `"0x18e4a2b3c0010003"`) rather than raw bigints because MessagePack's integer type is 64-bit signed, which can't represent the full HLC range without ambiguity across languages. Hex strings are unambiguous, human-readable in dumps, and trivially parsed with `BigInt(hexStr)`.

File naming convention: `deltas/{siteId}_{seq:010}.delta.bin`

Example: `deltas/a1b2c3d4_0000000001.delta.bin`

### 6.2 Segment File

A segment file contains the **merged CRDT state** for a set of rows, produced by compaction. It is a single MessagePack-encoded object:

```typescript
type SegmentFile = {
  v: 1;                       // format version
  table: string;              // which table this segment covers
  partition: string;          // partition key value (e.g., user_id hash prefix)
  hlc_max: string;            // hex-encoded bigint, latest HLC incorporated
  row_count: number;
  bloom: Uint8Array;          // serialized bloom filter over primary keys
  bloom_k: number;            // number of hash functions for the bloom filter
  rows: SegmentRow[];         // sorted by primary key
};

type SegmentRow = {
  key: MsgpackValue;          // primary key value
  cols: Record<string, CrdtState>;
};

type CrdtState =
  | { t: 1; hlc: string; site: string; val: MsgpackValue }    // LWW Register
  | { t: 2; inc: Record<string, number>; dec: Record<string, number> }  // PN Counter
  | {
      t: 3;
      elems: Array<{ val: MsgpackValue; add_hlc: string; add_site: string }>;
      tombstones: Array<{ add_hlc: string; add_site: string }>;
    }  // OR-Set
  | { t: 4; vals: Array<{ val: MsgpackValue; hlc: string; site: string }> };  // MV Register
```

File naming convention: `segments/{table}_{partition}_{hlc_max_hex8}.seg.bin`

Example: `segments/tasks_u0a_18e4a2b3.seg.bin`

**Rows are sorted by primary key** (numeric comparison for numbers, lexicographic for strings). This enables binary search when the file is loaded into memory.

**The bloom filter** is over stringified primary keys (`String(key)`). Before scanning all rows, check the bloom filter for point lookups. False positive rate target: 1% with 10 bits per element.

### 6.3 Manifest File

The manifest is MessagePack (not JSON) for consistency, but also small enough that JSON would be fine. Using MessagePack means the same dump tool works.

```typescript
type Manifest = {
  v: 1;
  version: number;                 // monotonic, incremented on every compaction
  compaction_hlc: string;          // hex bigint: all ops ≤ this HLC are in segments
  segments: SegmentRef[];
  sites_compacted: Record<string, string>;  // siteId → last compacted LogPosition (as string)
};

type SegmentRef = {
  path: string;                    // e.g., "segments/tasks_u0a_18e4a2b3.seg.bin"
  table: string;
  partition: string;
  row_count: number;
  size_bytes: number;
  hlc_max: string;
  key_min: MsgpackValue;           // smallest primary key in this segment
  key_max: MsgpackValue;           // largest primary key in this segment
};
```

The manifest lives at a well-known path: `manifest.bin`

### 6.4 Schema File

Stored locally and in the replication backend at `schema.bin`:

```typescript
type SchemaFile = {
  v: 1;
  tables: TableDef[];
};

type TableDef = {
  name: string;
  pk: string;                      // primary key column name
  pk_type: "string" | "number";
  partition_by: string | null;     // column used for partitioning (e.g., "owner_id")
  columns: ColumnDef[];
};

type ColumnDef = {
  name: string;
  crdt_type: "lww" | "pn_counter" | "or_set" | "mv_register";
  value_type: "string" | "number" | "boolean" | "null";
};
```

---

## 7. CRDT Types

Four CRDT types, identified by numeric tags in the binary format.

### 7.1 LWW Register (tag = 1)

Last-Writer-Wins. Stores a single value with an HLC timestamp and site ID.

**State:** `{ hlc, site, value }`

**Merge:** Compare HLC. Higher HLC wins. If HLCs are equal, higher site ID (lexicographic) wins.

**Op payload (`val` field in EncodedOp):** The new value directly. The HLC and site come from the op's own `hlc` and `site` fields.

### 7.2 PN-Counter (tag = 2)

Positive-Negative Counter. Two maps of `siteId → count`.

**State:** `{ inc: { site_a: 5, site_b: 3 }, dec: { site_a: 1 } }`

**Current value:** `sum(inc.values()) - sum(dec.values())`

**Merge:** For each site key, take `max(local[site], remote[site])` independently for both `inc` and `dec` maps.

**Op payload:** `{ d: "inc" | "dec", n: number }` — direction and amount. Applied by: `state[d][op.site] = (state[d][op.site] ?? 0) + n`.

Note: ops are not idempotent for PN-Counters. The engine must deduplicate ops by `(site, hlc)` before applying. The ReplicatedLog guarantees this via positional ordering — an op at position N from site X is applied exactly once.

### 7.3 OR-Set (tag = 3)

Observed-Remove Set. Each element has a unique add-tag (hlc + site).

**State:** `{ elems: [{ val, add_hlc, add_site }], tombstones: [{ add_hlc, add_site }] }`

**Current value:** The set of distinct `val` values across all elements whose add-tag does **not** appear in `tombstones`.

**Merge:** Union `elems` and union `tombstones`, then filter out any element whose `(add_hlc, add_site)` appears in `tombstones`.

**Op payload:** `{ a: "add", val: V }` or `{ a: "rmv", tags: Array<{ hlc: string, site: string }> }`. Remove specifies exact add-tags to remove (the client must have observed them).

### 7.4 MV-Register (tag = 4)

Multi-Value Register. Like LWW but keeps ALL concurrent values. Useful when you want to surface conflicts to the application.

**State:** `{ values: [{ val, hlc, site }] }`

**Current value:** Array of all values (if length > 1, there's an unresolved conflict).

**Merge:** Keep all values whose HLC is not dominated by another value's HLC. Value A dominates value B if A.hlc > B.hlc AND they are from the same causal lineage. In practice (without vector clocks): keep all values, discard any where another value has strictly higher HLC from the same site. If unsure, keep both — the application resolves.

**Op payload:** Same as LWW. The new value directly.

---

## 8. SQL Dialect

Minimal subset. No joins, no subqueries, no GROUP BY, no ORDER BY (results are always in primary key order).

### 8.1 DDL

```sql
CREATE TABLE tasks (
  id       STRING PRIMARY KEY,
  title    LWW<STRING>,
  done     LWW<BOOLEAN>,
  priority LWW<NUMBER>,
  points   COUNTER,
  tags     SET<STRING>,
  status   REGISTER<STRING>
) PARTITION BY owner_id;
```

Type mapping:
- `LWW<T>` → LWW Register (tag 1)
- `COUNTER` → PN Counter (tag 2)
- `SET<T>` → OR-Set (tag 3)
- `REGISTER<T>` → MV Register (tag 4)

`PARTITION BY` names the column used to determine which segment file a row belongs to. If omitted, all rows go into a single partition `"_default"`.

`DROP TABLE name;` removes the table from the schema. Segment and delta files are not cleaned up (compaction ignores tables not in the schema).

### 8.2 DML

**INSERT** creates a row with initial CRDT state:

```sql
INSERT INTO tasks (id, title, done, points) VALUES ('t1', 'Ship it', false, 0);
```

Semantics: For each column, emit one CrdtOp. LWW columns get a SET op, COUNTER gets an INC with the initial value, SET gets ADDs for each element.

If a row with the same PK already exists, INSERT behaves as an upsert — the CRDT merge handles it (LWW takes latest, counters accumulate, etc.). There is no INSERT-or-error behavior.

**UPDATE** modifies specific columns:

```sql
UPDATE tasks SET title = 'Ship it now', done = true WHERE id = 't1';
```

The WHERE clause must be an exact primary key match (`pk = value`) or a partition key match (`partition_col = value`). No range updates, no computed expressions.

**INC/DEC** for counters:

```sql
INC tasks.points BY 5 WHERE id = 't1';
DEC tasks.points BY 2 WHERE id = 't1';
```

These are sugar for emitting PN-Counter ops. They cannot be expressed as standard UPDATE because `SET points = points + 5` implies a read-modify-write that doesn't compose as a CRDT.

**ADD/REMOVE** for sets:

```sql
ADD 'urgent' TO tasks.tags WHERE id = 't1';
REMOVE 'urgent' FROM tasks.tags WHERE id = 't1';
```

REMOVE requires that the client has observed the element (it removes by add-tag, not by value). If the element hasn't been observed locally, REMOVE is a no-op.

**SELECT** reads data:

```sql
SELECT id, title, points FROM tasks WHERE owner_id = 'alice';
SELECT * FROM tasks WHERE id = 't1';
SELECT id, title FROM tasks WHERE owner_id = 'alice' AND done = false;
```

Supported WHERE operators: `=`, `!=`, `<`, `>`, `<=`, `>=`, `AND`. No `OR`, no `LIKE`, no functions.

Multiple conditions are ANDed. At least one condition should match either the PK or the partition key for the query planner to select the right segment file. If no partition condition is present, all segments for the table are scanned.

**DELETE:**

```sql
DELETE FROM tasks WHERE id = 't1';
```

Implemented as a tombstone: a special LWW register on a hidden `_deleted` column set to `true`. Reads filter out tombstoned rows. Compaction retains tombstones until a configurable TTL (default: 7 days), after which they are dropped.

---

## 9. Query Execution

### 9.1 Write Path

```
User executes: UPDATE tasks SET title = 'X' WHERE id = 't1';
  │
  ├─ 1. SQL parser → AST → validate against schema
  ├─ 2. Generate CrdtOps:
  │      [{ tbl: "tasks", key: "t1", col: "title", typ: 1, hlc: clock.now(), site: mySite, val: "X" }]
  ├─ 3. Apply ops to local state (in-memory merge over loaded segments)
  ├─ 4. Append ops to local write buffer (StorageAdapter)
  └─ 5. When sync() is called: flush write buffer → ReplicatedLog.append()
```

Step 3 ensures reads reflect local writes immediately (read-your-writes). Step 5 is async and can happen on a timer, on network reconnect, or explicitly.

### 9.2 Read Path

```
User executes: SELECT * FROM tasks WHERE owner_id = 'alice' AND done = false;
  │
  ├─ 1. SQL parser → AST → validate against schema
  ├─ 2. Query planner:
  │      - Table: tasks, partition_by: owner_id
  │      - WHERE has owner_id = 'alice' → resolve to partition "alice"
  │      - Need segment: segments/tasks_alice_*.seg.bin
  ├─ 3. Load segment from StorageAdapter (cached in memory after first load)
  ├─ 4. Apply any uncompacted local ops on top (overlay)
  ├─ 5. Scan rows:
  │      - For each row: materialize CRDT state → plain values
  │      - Apply remaining WHERE filters (done = false)
  │      - Apply projection (SELECT columns)
  └─ 6. Return Row[]
```

**Materialization** converts CRDT state to plain values:
- LWW Register → its value
- PN-Counter → sum(inc) - sum(dec)
- OR-Set → array of distinct values
- MV-Register → if single value, that value; if multiple, an array (application decides)

### 9.3 Local Query Routing

All queries run locally. There is no server query path in v1.

If a query requires data from a partition not available locally (e.g., user asks for `WHERE owner_id = 'bob'` but only Alice's partition is synced), the engine returns an error: `PartitionNotAvailable { table: "tasks", partition: "bob" }`.

The application layer decides how to handle this (fetch from server, show error, etc.).

---

## 10. Sync Protocol

### 10.1 Pushing Local Changes

```
sync_push():
  1. Read local write buffer from StorageAdapter ("local/pending_ops.bin")
  2. If empty → done
  3. Package ops into a LogEntry { siteId, hlc, ops }
  4. Call ReplicatedLog.append(entry)
  5. On success: clear local write buffer
  6. On failure (network): keep buffer, retry later
```

### 10.2 Pulling Remote Changes

```
sync_pull():
  1. For each known remote site (from ReplicatedLog.listSites()):
     a. Read local bookmark: "What LogPosition did I last sync from this site?"
        (Stored in StorageAdapter at "sync/{siteId}.bookmark")
     b. Call ReplicatedLog.readSince(siteId, bookmark)
     c. For each LogEntry received:
        - Apply ops to local state (CRDT merge)
        - Update bookmark
  2. Also check for updated manifest from SnapshotStore (if using compaction):
     a. getManifest()
     b. If manifest.version > local version:
        - Download any new/changed segment files
        - Update local manifest cache
        - Fast-forward bookmarks based on manifest.sites_compacted
```

### 10.3 Conflict Between Deltas and Segments

A client may have both:
- A locally-applied delta from site X at position 5
- A segment that was compacted including site X up to position 7

This is fine. CRDT merge is idempotent for state-based types (LWW, OR-Set, MV-Register). For PN-Counter, the segment contains the compacted counter state (max per site), and applying the same increment op twice would be wrong. Therefore:

**Rule:** When a new manifest is loaded, discard any locally-cached deltas from sites whose bookmark is ≤ `manifest.sites_compacted[siteId]`. The segment already includes those ops. Only apply deltas with positions strictly greater than the compacted position.

---

## 11. Compaction

A single cronjob. Does not delete files. Can run from anywhere.

```
compact():
  1. Read current manifest from SnapshotStore (or create empty if none)
  2. Read schema from SnapshotStore
  3. List all sites from ReplicatedLog
  4. For each site:
     a. Read all entries since manifest.sites_compacted[site] (or 0n if first run)
     b. Collect all ops
  5. For each table in schema:
     a. Group ops by partition key value
     b. For each partition:
        i.   Load existing segment (if any) → current CRDT state per row
        ii.  Apply all new ops → merged state
             - OR-Set remove ops record their remove-tags in `tombstones` (do not discard).
             - OR-Set materialization and merges must suppress any element whose add-tag appears in `tombstones`.
        iii. Build bloom filter over primary keys
        iv.  Sort rows by primary key
        v.   Encode as SegmentFile (§6.2)
        vi.  PUT to SnapshotStore
  6. Build new manifest:
     - Updated segment references
     - Updated sites_compacted (site → latest LogPosition seen)
     - compaction_hlc = max HLC seen across all ops
     - version = old_version + 1
  7. CAS manifest: putManifest(newManifest, oldManifest.version)
     - If CAS fails: another compaction ran concurrently. Discard work, retry next cycle.
     - Orphaned segment files from failed CAS are harmless (unreferenced, waste storage only)
```

**No deletions.** Old segment files and old delta files remain in storage. They are never downloaded by clients (clients only fetch segments listed in the manifest, and deltas newer than the compaction watermark). Storage cost is negligible for small-to-medium datasets.

**Frequency:** Run every N minutes. For development, manual trigger is fine. For production, a cron schedule (e.g., every 5 minutes). If write volume is low, every hour or even daily is fine — clients still get fresh data from the ReplicatedLog deltas directly.

---

## 12. Replication Backends

### 12.1 In-Memory Server

An HTTP server holding all state in memory (or backed by a single JSON file for persistence across restarts).

```
Routes:
  POST   /logs/:siteId              → append entry, returns { pos }
  GET    /logs/:siteId?since=N      → returns entries since position N
  GET    /logs                      → returns list of site IDs
  GET    /logs/:siteId/head         → returns latest position

  GET    /manifest                  → returns manifest bytes (or 404)
  PUT    /manifest?expect_version=N → CAS manifest (412 Precondition Failed if version mismatch)
  GET    /segments/:path            → returns segment bytes
  PUT    /segments/:path            → upload segment
  GET    /schema                    → returns schema bytes
  PUT    /schema                    → upload schema
```

Request/response bodies are raw MessagePack bytes with `Content-Type: application/x-msgpack`. This keeps the implementation trivial — the server does no parsing, it just stores and retrieves byte blobs. The only logic is the CAS check on manifest version.

For development: start with `bun serve` or `node:http`. Single file, < 100 lines of handler code.

Persistence: optionally write each log and the manifest to a directory as `.bin` files. On startup, scan the directory to reload state.

### 12.2 Tigris S3

Maps the ReplicatedLog and SnapshotStore interfaces onto S3 operations:

```
ReplicatedLog:
  append(entry)             → PUT deltas/{siteId}_{seq:010}.delta.bin
  readSince(siteId, since)  → LIST deltas/{siteId}_* → filter by seq > since → GET each
  listSites()               → LIST deltas/ with delimiter "/" → extract site prefixes
  getHead(siteId)           → LIST deltas/{siteId}_* → parse max seq from filenames

SnapshotStore:
  getManifest()             → GET manifest.bin (with X-Tigris-Consistent:true)
  putManifest(m, expected)  → GET current ETag → compare version → PUT with If-Match ETag
  getSegment(path)          → GET {path}
  putSegment(path, data)    → PUT {path}
```

**Consistency for manifest:** Use `X-Tigris-Consistent: true` header on GET and the If-Match ETag conditional on PUT. This routes through the global leader, ensuring the CAS is correct regardless of which region the compaction job runs in.

**Consistency for deltas:** Default (eventual) consistency is fine. Worst case, a sync pull misses a very recent delta — it catches up on the next pull. CRDTs guarantee convergence.

**Browser access:** Use presigned URLs. A lightweight auth endpoint (Cloudflare Worker, Lambda, etc.) takes an auth token and returns presigned GET/PUT URLs for the user's partition. The browser then uses raw `fetch()` against those URLs. No S3 SDK needed in the browser.

---

## 13. CLI Tool

```bash
# Dump any binary file to pretty-printed JSON
crdtbase dump path/to/file.bin

# Dump with type annotations (shows CRDT type tags as names)
crdtbase dump path/to/file.bin --annotate

# Inspect a segment: show row count, key range, bloom stats, partition
crdtbase inspect path/to/segment.seg.bin

# Inspect manifest: show segment listing, compaction watermark, versions
crdtbase inspect path/to/manifest.bin

# Validate a file against expected format
crdtbase validate path/to/file.bin --type delta|segment|manifest|schema

# Run a query against a local data directory
crdtbase query "SELECT * FROM tasks WHERE id = 't1'" --data ./data

# Show all rows in a segment as a table
crdtbase rows path/to/segment.seg.bin

# Show ops in a delta as a table
crdtbase ops path/to/file.delta.bin
```

### 13.1 Dump Format

The `dump` command decodes MessagePack to JSON with special handling:

- `Uint8Array` fields (bloom filters) are displayed as `"<bytes:1024>"` (showing length)
- HLC hex strings are annotated: `"0x18e4a2b3c0010003"` → `"0x18e4a2b3c0010003 (2024-01-15T10:30:00.000Z #3)"`
- CRDT type tags are annotated: `"t": 1` → `"t": "1 (LWW)"`

The `--annotate` flag enables these annotations. Without it, output is raw JSON (valid, parseable).

### 13.2 Rows Format

```
$ crdtbase rows segments/tasks_alice_18e4a2b3.seg.bin

table: tasks | partition: alice | rows: 3 | hlc_max: 2024-01-15T10:30:00.000Z

┌──────┬──────────────┬───────┬──────────┬────────┐
│ id   │ title        │ done  │ priority │ points │
├──────┼──────────────┼───────┼──────────┼────────┤
│ t1   │ Ship it      │ false │ 1        │ 5      │
│ t2   │ Write tests  │ true  │ 2        │ 3      │
│ t3   │ Deploy       │ false │ 1        │ 0      │
└──────┴──────────────┴───────┴──────────┴────────┘
```

This materializes CRDT state to plain values (same logic as query SELECT *).

### 13.3 Ops Format

```
$ crdtbase ops deltas/a1b2c3d4_0000000001.delta.bin

site: a1b2c3d4 | seq: 1 | ops: 4 | hlc_range: 2024-01-15T10:30:00-10:30:01

┌─────┬───────┬─────┬──────────┬──────┬──────────────────────┬───────────────┐
│ #   │ table │ key │ column   │ type │ hlc                  │ value         │
├─────┼───────┼─────┼──────────┼──────┼──────────────────────┼───────────────┤
│ 0   │ tasks │ t1  │ title    │ LWW  │ 10:30:00.000 #0      │ "Ship it"     │
│ 1   │ tasks │ t1  │ done     │ LWW  │ 10:30:00.000 #1      │ false         │
│ 2   │ tasks │ t1  │ priority │ LWW  │ 10:30:00.000 #2      │ 1             │
│ 3   │ tasks │ t1  │ points   │ CTR  │ 10:30:00.000 #3      │ +5            │
└─────┴───────┴─────┴──────────┴──────┴──────────────────────┴───────────────┘
```

---

## 14. Engine Lifecycle

```typescript
// Initialize
const engine = new CrdtEngine({
  storage: new FsStorageAdapter("./data"),
  log: new HttpReplicatedLog("http://localhost:8080"),
  snapshots: new FsSnapshotStore("./data"),
  siteId: generateSiteId(),   // UUIDv4 hex, persisted in storage on first run
});

// Load schema (from local cache or remote)
await engine.loadSchema();

// Execute DDL
await engine.exec("CREATE TABLE tasks (...)");

// Execute DML
await engine.exec("INSERT INTO tasks (id, title) VALUES ('t1', 'Hello')");
const rows = await engine.query("SELECT * FROM tasks WHERE id = 't1'");

// Sync
await engine.sync();  // push local changes + pull remote changes

// Close
await engine.close();
```

---

## 15. Implementation Order

Build and test in this order. Each phase is independently useful.

**Phase 1: Core primitives (no I/O)**
- [ ] HLC: pack, unpack, `now()`, `recv()`, comparison
- [ ] CRDT types: LWW merge, PNCounter merge, ORSet merge, MVRegister merge
- [ ] Encoding: MessagePack wrappers, delta file encode/decode, segment file encode/decode
- [ ] Bloom filter: create from keys, test membership, serialize/deserialize
- [ ] Tests: unit tests for every merge case, encode/decode round-trips

**Phase 2: CLI tool**
- [ ] `dump` command (decode any .bin file to JSON)
- [ ] `validate` command
- [ ] `rows` and `ops` display commands
- [ ] Manually create test fixtures and verify with dump

**Phase 3: SQL parser + engine (in-memory only)**
- [ ] Parser: CREATE TABLE, INSERT, UPDATE, SELECT, DELETE, INC/DEC, ADD/REMOVE
- [ ] Schema management (in-memory)
- [ ] Write path: SQL → CrdtOps → apply to in-memory state
- [ ] Read path: scan rows → materialize → filter → project
- [ ] Tests: SQL round-trip tests (insert then select)

**Phase 4: Storage + in-memory server**
- [ ] FsStorageAdapter (Node)
- [ ] MemoryReplicatedLog + HTTP server
- [ ] HttpReplicatedLog client
- [ ] FsSnapshotStore
- [ ] Sync protocol: push/pull
- [ ] Test: two engine instances syncing through in-memory server

**Phase 5: Compaction**
- [ ] Compaction job: read deltas → merge → write segments → CAS manifest
- [ ] Engine: load segments + overlay deltas
- [ ] Test: write → compact → read gives same results

**Phase 6: Browser**
- [ ] OpfsStorageAdapter
- [ ] Build with esbuild/vite targeting browser
- [ ] Simple test page: create table, insert, select, dump state

**Phase 7: Tigris**
- [ ] TigrisReplicatedLog (S3 LIST/GET/PUT)
- [ ] TigrisSnapshotStore (GET/PUT with ETag CAS)
- [ ] Presigned URL auth endpoint
- [ ] Test: Node engine syncing through Tigris, browser engine syncing through Tigris

---

## Appendix A: MessagePack Encoding Notes

`@msgpack/msgpack` encodes JavaScript types as follows. Know this to understand dump output:

| JS Type | MessagePack Type | Notes |
|---------|-----------------|-------|
| `null` | nil | |
| `boolean` | boolean | |
| `number` (integer) | int/uint | Automatically picks smallest encoding |
| `number` (float) | float64 | |
| `string` | str | UTF-8 |
| `Uint8Array` | bin | Raw bytes. Use for bloom filters. |
| `Array` | array | |
| `object` | map | String keys only |
| `bigint` | **NOT SUPPORTED** | Encode as hex string. This is why HLCs are hex strings. |

## Appendix B: Why Not [Alternative]?

**Why not Protobuf/FlatBuffers?** Require a schema compilation step, separate `.proto`/`.fbs` files, generated code. MessagePack is schema-less — you can dump any file without knowing its type. For a learning project, being able to `hexdump file.bin | head` and see recognizable MessagePack framing is invaluable.

**Why not JSON?** Size. A segment with 2000 rows and CRDT metadata would be ~2-5x larger as JSON. MessagePack is typically 30-50% smaller than JSON for the same data, and decode is ~3x faster (no string parsing).

**Why not a custom binary format?** Maximum debuggability sacrifice. Every custom format needs a custom parser, custom dump tool, custom documentation. MessagePack gives you `decode(bytes) → JSON` as a one-liner. The 10-20% size overhead vs a hand-rolled format is irrelevant at learning-project scale.

**Why not SQLite for local storage?** It would work, and cr-sqlite proves it. But the goal is to learn how a storage engine works from the ground up. Using SQLite hides the segment file design, the bloom filter, the merge logic, and the compaction process — which are the interesting parts.

## Appendix C: Size Estimates

For a task management app with 2000 tasks per user, 10 columns per task:

| Item | Estimated Size |
|------|---------------|
| One row (10 LWW columns, MessagePack) | ~200 bytes |
| Segment file (2000 rows) | ~400 KB |
| Bloom filter (2000 keys, 1% FPR) | ~2.4 KB |
| Delta file (50 ops) | ~10 KB |
| Manifest (20 segments) | ~4 KB |
| Total local storage per user | ~500 KB |

This fits comfortably in OPFS (browsers allow multi-GB) and syncs in a single HTTP request.
