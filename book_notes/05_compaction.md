# Chapter 5: Compaction

## 1. Why Compaction Exists

CRDTBase uses a **delta-shipping** replication model. Every write from every site
appends a small delta file to the replicated log:

```
deltas/site-a/0000000001.delta.bin
deltas/site-a/0000000002.delta.bin
deltas/site-b/0000000001.delta.bin
...
```

Without compaction, a new client joining the system must read every delta ever
written by every site, replay them all, and only then can it answer queries.
As the number of deltas grows, this becomes impractical:

- **Startup cost:** A fresh client downloads N deltas across S sites.
- **Read amplification:** Every query must overlay all uncompacted deltas on top
  of whatever base state exists.
- **Storage scan cost:** Listing and fetching thousands of small S3 objects is
  slow.

Compaction solves this by periodically folding accumulated deltas into
**segment files** -- pre-merged CRDT state snapshots. A new client only needs to
download the latest segments (listed in a manifest) and then replay only the
deltas that arrived *after* the last compaction.

This is conceptually similar to an LSM-tree (Log-Structured Merge Tree): the
"log" is the ReplicatedLog of deltas, and "compaction" merges the log entries
into sorted segment files. However, CRDTBase's design is simpler than a
traditional LSM-tree because:

1. There is only one level of segments (no tiered compaction).
2. Segments are partitioned by table and partition key, not by key range.
3. CRDT merge semantics replace the traditional "pick the newer value" merge
   policy.

## 2. Architecture Overview

Compaction involves three core abstractions:

| Abstraction | Role | Key files |
|---|---|---|
| **ReplicatedLog** | Source of truth: per-site append-only delta streams | `src/core/replication.ts` |
| **SnapshotStore** | Destination: stores segment files and the manifest | `src/core/snapshotStore.ts` |
| **Compactor** | The job that reads deltas, merges state, writes segments, and CAS-updates the manifest | `src/platform/node/compactor.ts` |

The core compaction data types and segment-building logic live in
`src/core/compaction.ts` (platform-independent). The orchestration that ties
together log reading, segment writing, and manifest CAS lives in
`src/platform/node/compactor.ts`.

## 3. Data Structures

### 3.1 SegmentFile

A segment file is a MessagePack-encoded blob containing the **merged CRDT state**
for all rows in one (table, partition) pair.

```typescript
// src/core/compaction.ts:18-27
export type SegmentFile = {
  v: 1;
  table: string;
  partition: string;
  hlc_max: string;        // hex-encoded HLC of latest incorporated op
  row_count: number;
  bloom: Uint8Array;       // bloom filter over primary keys
  bloom_k: number;         // number of hash functions
  rows: SegmentRow[];      // sorted by primary key
};

// src/core/compaction.ts:13-16
export type SegmentRow = {
  key: SqlPrimaryKey;
  cols: Record<string, SqlEvalColumnState>;
};
```

Each `SegmentRow` holds the full CRDT state for every column -- not just the
materialized value, but the complete state needed for future merges:

- **LWW Register (typ=1):** `{ val, hlc, site }` -- the winning value and its
  timestamp.
- **PN-Counter (typ=2):** `{ inc: Record<site, count>, dec: Record<site, count> }` --
  per-site increment and decrement tallies.
- **OR-Set (typ=3):** `{ elements: [...], tombstones: [...] }` -- all live
  add-tags plus remove tombstones.
- **MV-Register (typ=4):** `{ values: [{val, hlc, site}, ...] }` -- all
  concurrent values.

Key design decisions:
- **Rows are sorted by primary key** (line 323-325 in `compaction.ts`), enabling
  binary search for point lookups.
- **A bloom filter** is built over all primary keys (10 bits per element, ~1%
  false positive rate) to skip segment scans for point queries.

### 3.2 ManifestFile

The manifest is the single coordination point. It records which segments exist
and what has been compacted.

```typescript
// src/core/compaction.ts:40-46
export type ManifestFile = {
  v: 1;
  version: number;                          // monotonic, incremented each compaction
  compaction_hlc: string;                   // max HLC across all compacted ops
  segments: ManifestSegmentRef[];           // pointers to segment files
  sites_compacted: Record<string, number>;  // siteId -> last compacted seq
};
```

The `sites_compacted` map is the **compaction watermark**: it tells clients
exactly which deltas are already folded into the segments. Any delta with
`seq <= sites_compacted[siteId]` is already in the segments and need not be
replayed.

Each `ManifestSegmentRef` carries metadata for fast query routing without
downloading the segment:

```typescript
// src/core/compaction.ts:29-38
export type ManifestSegmentRef = {
  path: string;           // e.g. "segments/tasks__default_18e4a2b3.seg.bin"
  table: string;
  partition: string;
  row_count: number;
  size_bytes: number;
  hlc_max: string;
  key_min: SqlPrimaryKey; // smallest PK in segment
  key_max: SqlPrimaryKey; // largest PK in segment
};
```

### 3.3 Empty Manifest

When no compaction has ever run, the system uses an empty manifest:

```typescript
// src/core/compaction.ts:393-401
export function makeEmptyManifest(): ManifestFile {
  return {
    v: 1,
    version: 0,
    compaction_hlc: '0x0',
    segments: [],
    sites_compacted: {},
  };
}
```

## 4. How Compaction Works Step by Step

The entry point is `compactReplicatedLog()` in
`src/platform/node/compactor.ts:56-131`.

### Step 1: Read Prior State

```typescript
// compactor.ts:59-68
const schema = options.schema ?? (await options.snapshots.getSchema());
const priorManifest = (await options.snapshots.getManifest()) ?? makeEmptyManifest();
const rows = await loadRowsFromManifest(options.snapshots, priorManifest);
const sitesCompacted: Record<string, number> = { ...priorManifest.sites_compacted };
let compactionHlc = priorManifest.compaction_hlc;
```

The compactor loads all existing segment files referenced by the prior manifest
and deserializes them back into `RuntimeRowState` -- the in-memory row
representation used by the CRDT engine. This is done by `loadRowsFromManifest()`
(compactor.ts:19-34), which iterates over each segment ref, fetches the bytes,
decodes the MessagePack, and converts segment rows into runtime rows via
`segmentFileToRuntimeRows()`.

### Step 2: Collect New Deltas from All Sites

```typescript
// compactor.ts:71-89
const sites = await options.log.listSites();
sites.sort();

for (const siteId of sites) {
  const since = normalizeSeq(sitesCompacted[siteId] ?? 0);
  const readEntries = await options.log.readSince(siteId, since);
  const entries = takeContiguousEntriesSince(readEntries, since);
  let nextHead = since;
  for (const entry of entries) {
    nextHead = Math.max(nextHead, normalizeSeq(entry.seq));
    compactionHlc = maxHlcHex(compactionHlc, entry.hlc);
    applyOpsToRuntimeRows(rows, entry.ops);
    for (const op of entry.ops) {
      compactionHlc = maxHlcHex(compactionHlc, op.hlc);
    }
    opsRead += entry.ops.length;
  }
  sitesCompacted[siteId] = nextHead;
}
```

For each site, the compactor reads entries strictly after the last compacted
sequence number. `takeContiguousEntriesSince()` (replication.ts:28-46) is a
safety mechanism -- it only advances through contiguous seq numbers
(`since+1, since+2, ...`), stopping at any gap. This prevents cursor skips under
eventually-consistent storage backends where higher-seq objects may appear before
lower-seq objects.

Each entry's CRDT ops are applied in order to the `rows` map via
`applyOpsToRuntimeRows()` (compaction.ts:226-233), which delegates to the
per-CRDT-type merge logic in `sqlEval.ts`.

### Step 3: Build New Segments

```typescript
// compactor.ts:91-104
const builtSegments = buildSegmentsFromRows({
  schema,
  rows,
  defaultHlcMax: compactionHlc,
});

const manifestSegments: ManifestSegmentRef[] = [];
const writtenSegments: string[] = [];
for (const built of builtSegments) {
  const bytes = encodeBin(built.segment);
  await options.snapshots.putSegment(built.path, bytes);
  manifestSegments.push(buildManifestSegmentRef(built.path, built.segment, bytes.byteLength));
  writtenSegments.push(built.path);
}
```

`buildSegmentsFromRows()` (compaction.ts:346-371) does the following:

1. **Group rows by (table, partition)** via `groupRowsByTableAndPartition()`
   (compaction.ts:272-301). The partition is resolved from the schema's
   `partitionBy` column.
2. **For each group, build a SegmentFile** via `buildSegmentFile()`
   (compaction.ts:317-344):
   - Sort rows by primary key.
   - Convert `RuntimeRowState` to `SegmentRow` (serializable CRDT state).
   - Build a bloom filter over the primary keys.
   - Compute `hlc_max` across all column states in the segment.
3. **Generate the segment file path** using
   `defaultSegmentPath()` (compaction.ts:313-315):
   ```
   segments/{table}_{partition}_{hlc_max_hex8}.seg.bin
   ```

Each built segment is MessagePack-encoded and PUT to the SnapshotStore.

### Step 4: CAS-Update the Manifest

```typescript
// compactor.ts:106-130
const nextManifest: ManifestFile = {
  v: 1,
  version: priorManifest.version + 1,
  compaction_hlc: compactionHlc,
  segments: manifestSegments,
  sites_compacted: sitesCompacted,
};

const applied = await options.snapshots.putManifest(nextManifest, priorManifest.version);
if (!applied) {
  const latestManifest = (await options.snapshots.getManifest()) ?? makeEmptyManifest();
  return {
    applied: false,
    manifest: latestManifest,
    writtenSegments: [],
    opsRead,
  };
}
```

The manifest is updated atomically via compare-and-swap: `putManifest()` only
succeeds if the current manifest version matches `priorManifest.version`. If
another compaction ran concurrently and bumped the version, the CAS fails and
this compaction's work is discarded. The orphaned segment files are harmless
(unreferenced, waste storage only).

The CAS implementations:

- **FsSnapshotStore** (`src/platform/node/fsSnapshotStore.ts:53-71`): Double-reads
  the manifest file before writing to reduce (but not eliminate) lost-update
  windows across processes.
- **TigrisSnapshotStore** (`src/backend/tigrisSnapshotStore.ts:132-175`): Uses
  S3 ETag-based conditional PUT (`IfMatch` / `IfNoneMatch`) for true CAS
  semantics.
- **HttpSnapshotStore** (`src/platform/node/httpSnapshotStore.ts:55-72`): Sends
  `PUT /manifest?expect_version=N` and checks for HTTP 412 (Precondition Failed).

## 5. What Triggers Compaction

Compaction is **not automatic or threshold-based**. It is a manually invoked or
cron-scheduled job.

From SPEC.md section 11:

> A single cronjob. Does not delete files. Can run from anywhere.

> **Frequency:** Run every N minutes. For development, manual trigger is fine.
> For production, a cron schedule (e.g., every 5 minutes). If write volume is
> low, every hour or even daily is fine -- clients still get fresh data from the
> ReplicatedLog deltas directly.

The compaction function `compactReplicatedLog()` is called directly in test code
and would be invoked by a scheduled job in production. There is no built-in
trigger mechanism watching delta counts or file sizes.

## 6. Before and After: What Files Exist

### Before first compaction

```
deltas/
  site-a/
    0000000001.delta.bin
    0000000002.delta.bin
    0000000003.delta.bin
  site-b/
    0000000001.delta.bin
    0000000002.delta.bin
schema.bin
```

No segments, no manifest. A new client must replay all deltas.

### After first compaction

```
deltas/                              (unchanged -- deltas are never deleted)
  site-a/
    0000000001.delta.bin
    0000000002.delta.bin
    0000000003.delta.bin
  site-b/
    0000000001.delta.bin
    0000000002.delta.bin
snapshots/
  manifest.bin                       (version: 1, sites_compacted: {site-a: 3, site-b: 2})
  segments/
    tasks__default_18e4a2b3.seg.bin  (merged state for all rows)
schema.bin
```

A new client reads only the manifest + segments. Zero deltas needed.

### After second compaction (with new deltas)

```
deltas/
  site-a/
    0000000001.delta.bin             (still here)
    ...
    0000000005.delta.bin             (new since last compaction)
  site-b/
    ...
    0000000004.delta.bin             (new since last compaction)
snapshots/
  manifest.bin                       (version: 2, sites_compacted: {site-a: 5, site-b: 4})
  segments/
    tasks__default_18e4a2b3.seg.bin  (old segment -- orphaned but not deleted)
    tasks__default_29f5b3c4.seg.bin  (new segment with all state merged)
schema.bin
```

Note: old segment files are **never deleted**. They become unreferenced once the
manifest points to new segments. Storage cost is accepted as negligible for
small-to-medium datasets.

### After second compaction (no new deltas -- idempotent case)

The e2e tests verify this case explicitly:

```typescript
// test/e2e/three-clients.e2e.test.ts:204-211
const secondCompaction = await compactReplicatedLog({
  log: logA,
  schema,
  snapshots,
});
expect(secondCompaction.applied).toBe(true);
expect(secondCompaction.opsRead).toBe(0);
expect(secondCompaction.manifest.sites_compacted).toEqual(
  compaction.manifest.sites_compacted,
);
```

When no new ops have arrived since the last compaction, `opsRead` is 0. The
compactor still rebuilds segments from the existing state and CAS-updates the
manifest (incrementing the version), but the segment content is identical.

## 7. How Compaction Preserves CRDT Correctness

The fundamental correctness property is:

> **Compacting a prefix of operations and then applying the remaining suffix
> produces the same final state as applying all operations from scratch.**

This is formally stated and proven in Lean 4.

### 7.1 The Lean Proof

The core theorem lives in `lean/CrdtBase/Compaction/Props.lean:36-45`:

```lean
/-- Canonical compaction law: compacting a prefix and folding the suffix
is equivalent to folding the full stream. -/
theorem compaction_preserves_state {α β : Type}
    (step : β → α → β) (init : β) (preOps postOps : List α) :
    List.foldl step (List.foldl step init preOps) postOps =
      List.foldl step init (preOps ++ postOps) := by
  exact
    (List.foldl_append
      (f := step)
      (b := init)
      (l := preOps)
      (l' := postOps)).symm
```

The proof is surprisingly simple: it follows directly from `List.foldl_append`,
which states that folding over a concatenation is the same as folding the first
list and then continuing with the second. This holds for *any* step function --
no commutativity or associativity required.

**Why this works for compaction:** Compaction takes a prefix of the operation
stream (`preOps`), folds it into a state (the segment), and then clients fold
the remaining operations (`postOps`) on top. The theorem says this two-phase
fold equals folding everything at once.

### 7.2 Per-CRDT-Type Specializations

The Lean proofs include specializations for each CRDT type, confirming that the
concrete merge functions satisfy the compaction law:

```lean
-- lean/CrdtBase/Compaction/Props.lean:55-103
theorem pn_counter_compaction_preserves_state ...
theorem or_set_compaction_preserves_state ...
theorem mv_register_compaction_preserves_state ...
theorem lww_compaction_preserves_state ...
```

Each uses `foldPrefixSuffix` (Defs.lean:13-15), which splits a list at an
arbitrary point and folds both halves:

```lean
def foldPrefixSuffix {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) (split : Nat) : β :=
  List.foldl step (List.foldl step init (ops.take split)) (ops.drop split)
```

### 7.3 Idempotence

The Lean code also proves that compacting an already-compacted state with no new
deltas is a no-op:

```lean
-- lean/CrdtBase/Compaction/Props.lean:48-52
theorem compaction_idempotent {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) (split : Nat) :
    foldPrefixSuffix step (foldPrefixSuffix step init ops split) [] split =
      foldPrefixSuffix step init ops split := by
  simp [foldPrefixSuffix]
```

### 7.4 The PN-Counter Subtlety

The SPEC calls out a critical subtlety for PN-Counters (SPEC.md lines 604-606):

> CRDT merge is idempotent for state-based types (LWW, OR-Set, MV-Register).
> For PN-Counter, the segment contains the compacted counter state (max per
> site), and applying the same increment op twice would be wrong.

For LWW, OR-Set, and MV-Register, merging the same state twice is harmless
(idempotent). But a PN-Counter increment of `+3` applied twice yields `+6`,
which is wrong. The system handles this with the **compaction watermark rule**:

> When a new manifest is loaded, discard any locally-cached deltas from sites
> whose last seq is <= `manifest.sites_compacted[siteId]`. The segment already
> includes those ops. Only apply deltas with seqs strictly greater than the
> compacted seq.

This is implemented in the client's `refreshFromSnapshotManifest()`:

```typescript
// src/platform/node/nodeClient.ts:385-389
// Reset site cursors to compaction watermarks so uncompacted deltas
// are replayed exactly once.
for (const [siteId, seq] of Object.entries(manifest.sites_compacted)) {
  this.syncedSeqBySite.set(siteId, seq);
  this.syncedHlcBySite.delete(siteId);
}
```

By resetting the per-site cursor to the compacted seq, subsequent delta pulls
start strictly *after* what the segment covers. No double-application occurs.

## 8. Tombstones and Garbage Collection

CRDTBase has two distinct tombstone mechanisms:

### 8.1 OR-Set Tombstones (Element-Level)

OR-Set removes are recorded as tombstones -- tags identifying which add
operations to suppress:

```typescript
// src/core/crdt/orSet.ts:13-16
export type OrSet<T> = {
  elements: Array<OrSetElement<T>>;
  tombstones: OrSetTag[];
};
```

During merge, any element whose add-tag appears in the tombstone set is filtered
out (orSet.ts:90-97). **Tombstones are never garbage-collected** -- they persist
in segment files to ensure that a removed element is not resurrected by a
delayed add operation from another site.

The SPEC confirms this for compaction (SPEC.md line 627):

> OR-Set remove ops record their remove-tags in `tombstones` (do not discard).

### 8.2 Row-Level Deletion (LWW Tombstone on `_deleted`)

Row-level `DELETE` is implemented as an LWW register write on a hidden
`_deleted` column set to `true`. From SPEC.md line 477:

> Implemented as a tombstone: a special LWW register on a hidden `_deleted`
> column set to `true`. Reads filter out tombstoned rows. Compaction retains
> tombstones until a configurable TTL (default: 7 days), after which they are
> dropped.

The TTL-based garbage collection of row tombstones is mentioned in the spec but
does not appear to be implemented yet in the current codebase. Compaction
currently retains all row states including deleted rows.

### 8.3 No File-Level Garbage Collection

Old segment files and old delta files are **never deleted** (SPEC.md line 643):

> **No deletions.** Old segment files and old delta files remain in storage.
> They are never downloaded by clients (clients only fetch segments listed in the
> manifest, and deltas newer than the compaction watermark). Storage cost is
> negligible for small-to-medium datasets.

This is a deliberate simplicity tradeoff. Unreferenced segment files are
harmless: clients only fetch segments listed in the current manifest. Old deltas
below the compaction watermark are similarly ignored by clients.

## 9. The Bloom Filter

Each segment includes a bloom filter over its primary keys, used to skip
segment scans for point lookups.

```typescript
// src/core/compaction.ts:179-205
export function buildBloomFilter(
  keys: SqlPrimaryKey[],
  bitsPerElement = 10,
): { bloom: Uint8Array; bloomK: number } {
  const requestedBitCount = Math.max(8, Math.ceil(keys.length * bitsPerElement));
  const byteCount = Math.ceil(requestedBitCount / 8);
  const bitCount = byteCount * 8;
  const bloom = new Uint8Array(byteCount);
  const bloomK = Math.max(1, Math.round((bitCount / keys.length) * Math.log(2)));
  // ...FNV-1a hashing with different seeds...
}
```

The filter uses FNV-1a hash with multiple seeds (one per hash function). The
number of hash functions `k` is computed optimally as
`round((bits/elements) * ln(2))`, which for the default 10 bits/element gives
approximately 7 hash functions and a ~1% false positive rate.

The bloom filter property test verifies no false negatives:

```typescript
// test/properties/compaction.prop.test.ts:186-191
test.prop([arbCompactionOps])('segment bloom filter has no false negatives', (ops) => {
  const segment = segmentForRows(applyOps(ops));
  for (const row of segment.rows) {
    expect(bloomMayContain(segment.bloom, segment.bloom_k, row.key)).toBe(true);
  }
});
```

## 10. Testing Strategy

Compaction correctness is tested at four levels:

### 10.1 Lean Formal Proofs (Tier 4)

Machine-checked proofs in `lean/CrdtBase/Compaction/` that compaction preserves
state for all CRDT types and is idempotent. These proofs cover the abstract
mathematical model.

### 10.2 Differential Random Testing (DRT)

`test/drt/compaction.drt.test.ts` runs property-based tests that verify the
TypeScript implementation agrees with the Lean oracle for the compaction split
law. For each CRDT type (LWW, PN-Counter, OR-Set, MV-Register):

1. Generate a random list of CRDT states.
2. For every possible split point, fold the prefix, then fold the suffix on top.
3. Verify the split result matches both the TypeScript direct fold and the Lean
   oracle direct fold.

```typescript
// test/drt/compaction.drt.test.ts:155-160
for (const splitIndex of splitPoints(states.length)) {
  const splitTs = applyCompactionSplitTs(states, splitIndex, mergeLww);
  const splitLean = await applyCompactionSplitLean(states, splitIndex, mergeLean);
  expect(splitTs).toEqual(directTs);
  expect(splitLean).toEqual(directLean);
}
```

### 10.3 Property-Based Tests

`test/properties/compaction.prop.test.ts` tests the full compaction pipeline
(including MessagePack encode/decode round-trip):

1. **Compaction preserves state** (line 150-168): Split ops at the midpoint,
   compact the prefix into a segment, encode/decode it, apply the suffix on top,
   and verify the result matches applying all ops directly.

2. **Compaction is idempotent** (line 170-175): Compact, encode, decode,
   re-compact, and verify the segment is identical.

3. **Rows are sorted** (line 177-184): Every segment has rows in primary key
   order.

4. **Bloom has no false negatives** (line 186-191): Every key in the segment is
   found by the bloom filter.

### 10.4 End-to-End Tests

`test/e2e/three-clients.e2e.test.ts` and `test/e2e/s3-minio.e2e.test.ts` test
the full integration:

1. Three sites write data through a shared replicated log.
2. All three sites sync and converge to the same state.
3. Compaction runs, producing segments and a manifest.
4. A **fourth client** (`site-d`) that has never seen any deltas joins, pulls the
   manifest and segments, and verifies it gets the same query results.
5. A second compaction with no new deltas verifies idempotence (`opsRead === 0`).

## 11. Client-Side Segment Consumption

When a client calls `pull()`, it checks for an updated manifest:

```typescript
// src/platform/node/nodeClient.ts:346-393
private async refreshFromSnapshotManifest(): Promise<void> {
  const manifest = await this.snapshots.getManifest();
  if (manifest === null || manifest.version <= this.localSnapshotManifestVersion) {
    return;
  }

  const rows = new Map<string, RuntimeRowState>();
  for (const segmentRef of manifest.segments) {
    const bytes = await this.snapshots.getSegment(segmentRef.path);
    const segment = decodeBin<SegmentFile>(bytes);
    const loaded = segmentFileToRuntimeRows(segment);
    mergeRuntimeRowMaps(rows, loaded);
  }

  // Preserve read-your-writes for local unpushed operations
  for (const pending of this.pendingOps) {
    applyCrdtOpToRows(rows, pending);
  }

  this.rows.clear();
  for (const [key, row] of rows.entries()) {
    this.rows.set(key, row);
  }

  // Reset site cursors to compaction watermarks
  for (const [siteId, seq] of Object.entries(manifest.sites_compacted)) {
    this.syncedSeqBySite.set(siteId, seq);
    this.syncedHlcBySite.delete(siteId);
  }
}
```

Key points:
- Segment files are downloaded and cached locally.
- The in-memory row state is rebuilt from segments, then pending (unpushed)
  local ops are re-applied to preserve read-your-writes consistency.
- Site cursors are reset to compaction watermarks, so subsequent delta pulls
  skip already-compacted entries.

## 12. Concurrency and Safety

### 12.1 CAS on the Manifest

The manifest version acts as an optimistic lock. If two compaction jobs race:

1. Both read manifest version N.
2. Both build new segments and attempt to write manifest version N+1.
3. Only one CAS succeeds. The other sees `applied: false` and discards its work.

Orphaned segment files from the losing compaction are harmless -- they are never
referenced by any manifest.

### 12.2 Contiguous Entry Safety

`takeContiguousEntriesSince()` (replication.ts:28-46) ensures the compactor
never skips over a gap in the log:

```typescript
export function takeContiguousEntriesSince(
  entries: readonly LogEntry[],
  since: LogPosition,
): LogEntry[] {
  const ordered = [...entries].sort((left, right) => left.seq - right.seq);
  const contiguous: LogEntry[] = [];
  let expected = since + 1;
  for (const entry of ordered) {
    if (entry.seq < expected) continue;
    if (entry.seq !== expected) break;
    contiguous.push(entry);
    expected += 1;
  }
  return contiguous;
}
```

Under eventually-consistent storage (like Tigris S3), a LIST operation might
return seq 5 and seq 7 but not yet seq 6. This function stops at seq 5, ensuring
the compaction watermark only advances over fully-observed deltas.

## 13. Performance Implications and Tradeoffs

| Aspect | Without compaction | With compaction |
|---|---|---|
| New client bootstrap | Read all deltas (O(total ops)) | Read segments + recent deltas (O(rows + recent ops)) |
| Read path | Replay all deltas | Load segment + overlay recent deltas |
| Write path | Unchanged (always append delta) | Unchanged |
| Storage | Deltas only | Deltas + segments + old orphaned segments |
| Coordination | None | CAS on manifest only |

**Tradeoffs accepted:**

1. **No file deletion:** Old segments and deltas accumulate. This simplifies the
   system (no distributed garbage collection) at the cost of storage growth.

2. **Full segment rewrite:** Every compaction rewrites all segments from scratch
   by reloading prior segments + new deltas. There is no incremental/partial
   compaction. This is acceptable at learning-project scale but would not scale
   to very large datasets.

3. **Single-level segments:** Unlike LSM-trees, there are no levels or tiers.
   Every compaction produces one segment per (table, partition) pair containing
   all rows. This keeps the design simple but means compaction cost is
   proportional to total data size, not just new data.

4. **Tombstone retention:** OR-Set tombstones are retained forever. Row-level
   delete tombstones are spec'd for TTL-based cleanup but not yet implemented.
   Both add to segment size over time.

## 14. Summary

Compaction in CRDTBase is a periodic batch job that folds accumulated delta
operations into pre-merged segment files, dramatically reducing the work needed
for new client bootstrap and query execution. Its correctness rests on a
formally verified property (the fold-append law) that holds for all CRDT types.
The design prioritizes simplicity and debuggability -- single-level segments,
no file deletion, MessagePack encoding for universal inspectability -- making it
an excellent learning implementation of a storage engine compaction system.
