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
| **Compactor** | The job that reads deltas, merges state, prunes tombstones, writes segments, and CAS-updates the manifest | `src/platform/node/compactor.ts` |

The core compaction data types, segment-building logic, and retention-policy
pruning live in `src/core/compaction.ts` (platform-independent). The
orchestration that ties together log reading, retention pruning, segment
writing, and manifest CAS lives in `src/platform/node/compactor.ts`.

## 3. Data Structures

### 3.1 SegmentFile

A segment file is a MessagePack-encoded blob containing the **merged CRDT state**
for all rows in one (table, partition) pair.

```typescript
// src/core/compaction.ts:19-28
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

// src/core/compaction.ts:14-17
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
  add-tags plus remove tombstones (subject to TTL-based pruning; see Section 8).
- **MV-Register (typ=4):** `{ values: [{val, hlc, site}, ...] }` -- all
  concurrent values.

Key design decisions:
- **Rows are sorted by primary key** (line 343-345 in `compaction.ts`), enabling
  binary search for point lookups.
- **A bloom filter** is built over all primary keys (10 bits per element, ~1%
  false positive rate) to skip segment scans for point queries.

### 3.2 ManifestFile

The manifest is the single coordination point. It records which segments exist
and what has been compacted.

```typescript
// src/core/compaction.ts:41-47
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
// src/core/compaction.ts:30-39
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

### 3.3 CompactionRetentionPolicy

The retention policy controls TTL-based tombstone garbage collection during
compaction:

```typescript
// src/core/compaction.ts:57-61
export type CompactionRetentionPolicy = {
  nowMs: number;
  orSetTombstoneTtlMs: number;
  rowTombstoneTtlMs: number;
};
```

Both TTLs default to 7 days (604,800,000 ms):

```typescript
// src/core/compaction.ts:54-55
export const DEFAULT_OR_SET_TOMBSTONE_TTL_MS = 7 * 24 * 60 * 60 * 1000;
export const DEFAULT_ROW_TOMBSTONE_TTL_MS = 7 * 24 * 60 * 60 * 1000;
```

The defaults are chosen so that any site offline for less than 7 days will sync
all its pending adds before tombstones are garbage-collected. After 7 days, the
system accepts the possibility that a very-delayed add could be spuriously
resurrected -- a practical tradeoff for bounded storage growth.

### 3.4 Empty Manifest

When no compaction has ever run, the system uses an empty manifest:

```typescript
// src/core/compaction.ts:413-421
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
`src/platform/node/compactor.ts:62-143`.

### Step 1: Read Prior State

```typescript
// compactor.ts:65-74
const schema = options.schema ?? (await options.snapshots.getSchema());
if (!schema) {
  throw new Error('compaction requires schema: provide options.schema or snapshots.getSchema()');
}

const priorManifest = (await options.snapshots.getManifest()) ?? makeEmptyManifest();
const rows = await loadRowsFromManifest(options.snapshots, priorManifest);
const sitesCompacted: Record<string, number> = { ...priorManifest.sites_compacted };
let compactionHlc = priorManifest.compaction_hlc;
```

The compactor loads all existing segment files referenced by the prior manifest
and deserializes them back into `RuntimeRowState` -- the in-memory row
representation used by the CRDT engine. This is done by `loadRowsFromManifest()`
(compactor.ts:22-37), which iterates over each segment ref, fetches the bytes,
decodes the MessagePack, and converts segment rows into runtime rows via
`segmentFileToRuntimeRows()`.

### Step 2: Collect New Deltas from All Sites

```typescript
// compactor.ts:80-95
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
sequence number. `takeContiguousEntriesSince()` (replication.ts) is a
safety mechanism -- it only advances through contiguous seq numbers
(`since+1, since+2, ...`), stopping at any gap. This prevents cursor skips under
eventually-consistent storage backends where higher-seq objects may appear before
lower-seq objects.

Each entry's CRDT ops are applied in order to the `rows` map via
`applyOpsToRuntimeRows()` (compaction.ts:246-253), which delegates to the
per-CRDT-type merge logic in `sqlEval.ts`.

### Step 3: Prune Expired Tombstones (Retention Policy)

After all new deltas are applied but before building segments, the compactor
prunes expired tombstones:

```typescript
// compactor.ts:97-101
pruneRuntimeRowsForCompaction(rows, {
  nowMs: (options.now ?? (() => Date.now()))(),
  orSetTombstoneTtlMs: options.orSetTombstoneTtlMs ?? DEFAULT_OR_SET_TOMBSTONE_TTL_MS,
  rowTombstoneTtlMs: options.rowTombstoneTtlMs ?? DEFAULT_ROW_TOMBSTONE_TTL_MS,
});
```

The `pruneRuntimeRowsForCompaction()` function (compaction.ts:423-464)
performs two kinds of cleanup:

1. **Row tombstone removal:** If a row's `_exists` column is an LWW register
   with value `false` and the HLC wall-clock time is older than
   `nowMs - rowTombstoneTtlMs`, the entire row is deleted from the map.

2. **OR-Set tombstone pruning:** For every OR-Set column in every remaining row,
   tombstone entries whose `addHlc.wallMs` is older than
   `nowMs - orSetTombstoneTtlMs` are filtered out, and the OR-Set is
   re-canonicalized via `canonicalizeOrSet()`.

Key implementation details:

- The cutoff comparison uses `isHlcExpired(wallMs, cutoffMs)` which returns
  `wallMs <= cutoffMs` -- the cutoff is inclusive.
- After filtering OR-Set tombstones, `canonicalizeOrSet()` re-normalizes the
  OR-Set for deterministic serialization order.
- Input validation via `assertFiniteNonNegativeMs()` guards against accidental
  `NaN` or `Infinity` TTL values that could silently prune everything or nothing.

### Step 4: Build New Segments

```typescript
// compactor.ts:103-116
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

`buildSegmentsFromRows()` (compaction.ts:366-391) does the following:

1. **Group rows by (table, partition)** via `groupRowsByTableAndPartition()`
   (compaction.ts:292-321). The partition is resolved from the schema's
   `partitionBy` column.
2. **For each group, build a SegmentFile** via `buildSegmentFile()`
   (compaction.ts:337-364):
   - Sort rows by primary key.
   - Convert `RuntimeRowState` to `SegmentRow` (serializable CRDT state).
   - Build a bloom filter over the primary keys.
   - Compute `hlc_max` across all column states in the segment.
3. **Generate the segment file path** using
   `defaultSegmentPath()` (compaction.ts:333-335):
   ```
   segments/{table}_{partition}_{hlc_max_hex8}.seg.bin
   ```

Each built segment is MessagePack-encoded and PUT to the SnapshotStore.

Because tombstone pruning happens *before* segment building, the segments
produced after retention pruning are smaller than they would be without it --
expired tombstones and deleted rows no longer occupy space in the serialized
segment files.

### Step 5: CAS-Update the Manifest

```typescript
// compactor.ts:118-135
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

The `SnapshotCompactorOptions` type (compactor.ts:46-53) allows callers to
customize retention behavior: `now` (defaults to `Date.now()`) is injectable for
testing, and `orSetTombstoneTtlMs`/`rowTombstoneTtlMs` override the default
7-day TTLs. Stress tests use short TTLs (e.g. 1ms) to exercise pruning paths.

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
and would be invoked by a scheduled job in production. In the stress test
harness, one designated worker runs compaction every 30 operations to exercise
the interleaving of compaction with concurrent writes.

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

The core definitions live in `lean/CrdtBase/Compaction/Defs.lean`:

```lean
-- lean/CrdtBase/Compaction/Defs.lean:12-15
/-- Apply a split compaction strategy: fold `take split`, then continue with `drop split`. -/
def foldPrefixSuffix {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) (split : Nat) : β :=
  List.foldl step (List.foldl step init (ops.take split)) (ops.drop split)
```

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

An equivalent formulation using `foldPrefixSuffix` is also proven for all
split points simultaneously (Props.lean:27-32):

```lean
theorem foldPrefixSuffix_eq_foldl_all {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) :
    ∀ split : Nat, foldPrefixSuffix step init ops split = List.foldl step init ops := by
  intro split
  simpa using foldPrefixSuffix_eq_foldl step init ops split
```

### 7.2 Per-CRDT-Type Specializations

The Lean proofs include specializations for each CRDT type, confirming that the
concrete merge functions satisfy the compaction law:

```lean
-- lean/CrdtBase/Compaction/Props.lean:54-102
theorem pn_counter_compaction_preserves_state
    (ops : List PnCounter) (split : Nat) :
    foldPrefixSuffix PnCounter.merge pnCounterEmpty ops split =
      List.foldl PnCounter.merge pnCounterEmpty ops

theorem or_set_compaction_preserves_state {α Hlc : Type}
    [DecidableEq α] [DecidableEq Hlc]
    (ops : List (OrSet α Hlc)) (split : Nat) :
    foldPrefixSuffix OrSet.merge (orSetEmpty α Hlc) ops split =
      List.foldl OrSet.merge (orSetEmpty α Hlc) ops

theorem mv_register_compaction_preserves_state {α : Type}
    [DecidableEq α]
    (ops : List (MvRegister α)) (split : Nat) :
    foldPrefixSuffix MvRegister.merge (mvRegisterEmpty α) ops split =
      List.foldl MvRegister.merge (mvRegisterEmpty α) ops

theorem lww_compaction_preserves_state {α : Type}
    (ops : List (LwwRegister α)) (split : Nat) :
    foldPrefixSuffix lwwStep none ops split =
      List.foldl lwwStep none ops
```

Each per-CRDT proof uses `foldPrefixSuffix_eq_foldl` instantiated with the
concrete merge function and empty initial state for that CRDT type (defined in
Defs.lean:18-29 as `pnCounterEmpty`, `orSetEmpty`, `mvRegisterEmpty`).

### 7.3 Snapshot Cutover Law

The snapshot cutover law (Props.lean:104-109) states that loading a compacted
prefix state and replaying suffix deltas is equivalent to replaying the full
stream. This directly models the client behavior of loading segments then pulling
trailing deltas:

```lean
theorem snapshot_then_suffix_replay_eq_full_fold {α β : Type}
    (step : β → α → β) (init : β) (compactedPrefix suffix : List α) :
    List.foldl step (List.foldl step init compactedPrefix) suffix =
      List.foldl step init (compactedPrefix ++ suffix) := by
  simpa using compaction_preserves_state step init compactedPrefix suffix
```

A further corollary (Props.lean:112-116) shows that when no new suffix deltas
exist, the snapshot cutover is a no-op:

```lean
theorem snapshot_cutover_idempotent_without_new_suffix {α β : Type}
    (step : β → α → β) (init : β) (compactedPrefix : List α) :
    List.foldl step (List.foldl step init compactedPrefix) [] =
      List.foldl step init compactedPrefix := by
  simp
```

### 7.4 Idempotence

The Lean code proves that compacting an already-compacted state with no new
deltas is a no-op:

```lean
-- lean/CrdtBase/Compaction/Props.lean:48-52
theorem compaction_idempotent {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) (split : Nat) :
    foldPrefixSuffix step (foldPrefixSuffix step init ops split) [] split =
      foldPrefixSuffix step init ops split := by
  simp [foldPrefixSuffix]
```

### 7.5 Summary of Lean Compaction Theorems

The Lean proofs contain **10 compaction theorems** total:

| Theorem | Line | What it proves |
|---|---|---|
| `foldPrefixSuffix_eq_foldl` | 10 | Split compaction = full fold |
| `foldPrefixSuffix_eq_foldl_all` | 28 | Above holds for all split points |
| `compaction_preserves_state` | 36 | Canonical prefix+suffix = full fold |
| `compaction_idempotent` | 48 | Re-compacting with no new data is identity |
| `pn_counter_compaction_preserves_state` | 55 | PN-counter specialization |
| `or_set_compaction_preserves_state` | 67 | OR-Set specialization |
| `mv_register_compaction_preserves_state` | 80 | MV-register specialization |
| `lww_compaction_preserves_state` | 93 | LWW specialization |
| `snapshot_then_suffix_replay_eq_full_fold` | 105 | Snapshot cutover law |
| `snapshot_cutover_idempotent_without_new_suffix` | 112 | No-op when no new deltas |

### 7.6 The PN-Counter Subtlety

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
// src/platform/node/nodeClient.ts:424-428
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

CRDTBase has two distinct tombstone mechanisms, and both now support TTL-based
garbage collection during compaction.

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
out (orSet.ts:90-97).

**Tombstone TTL-based pruning:** During compaction, OR-Set tombstones whose
`addHlc.wallMs` is older than `nowMs - orSetTombstoneTtlMs` are removed. The
default TTL is 7 days. After pruning, `canonicalizeOrSet()` re-normalizes the
OR-Set to maintain deterministic serialization order.

The implementation (compaction.ts:445-463):

```typescript
for (const [column, state] of row.columns.entries()) {
  if (state.typ !== 3) {
    continue;
  }
  const retainedTombstones = state.state.tombstones.filter(
    (tag) => !isHlcExpired(tag.addHlc.wallMs, orSetCutoffMs),
  );
  if (retainedTombstones.length === state.state.tombstones.length) {
    continue;       // no tombstones expired -- skip re-canonicalization
  }
  row.columns.set(column, {
    typ: 3,
    state: canonicalizeOrSet({
      elements: state.state.elements,
      tombstones: retainedTombstones,
    }),
  });
}
```

**Safety note:** Once an OR-Set tombstone is pruned, a very-delayed add with a
matching tag from an offline site could cause a "ghost resurrection" of the
removed element. The 7-day TTL is a practical ceiling: if a site is offline for
longer than 7 days, some data anomalies are accepted.

### 8.2 Row-Level Deletion (LWW Tombstone on `_deleted`)

Row-level `DELETE` is implemented as an LWW register write on a hidden
`_exists` column set to `false`. From SPEC.md line 477:

> Implemented as a tombstone: a special LWW register on a hidden `_deleted`
> column set to `true`. Reads filter out tombstoned rows. Compaction retains
> tombstones until a configurable TTL (default: 7 days), after which they are
> dropped.

**Row tombstone TTL-based removal:** During compaction, if a row's `_exists`
column is an LWW register with value `false` and the HLC wall-clock time is
older than `nowMs - rowTombstoneTtlMs`, the entire row is deleted from the
in-memory map before segment building (compaction.ts:434-443):

```typescript
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

After pruning, the deleted row no longer appears in any segment file, reducing
storage and speeding up scans.

### 8.3 No File-Level Garbage Collection

Old segment files and old delta files are **never deleted** (SPEC.md line 643):

> **No deletions.** Old segment files and old delta files remain in storage.
> They are never downloaded by clients (clients only fetch segments listed in the
> manifest, and deltas newer than the compaction watermark). Storage cost is
> negligible for small-to-medium datasets.

This is a deliberate simplicity tradeoff. Unreferenced segment files are
harmless: clients only fetch segments listed in the current manifest. Old deltas
below the compaction watermark are similarly ignored by clients.

## 9. Snapshot Cutover Coverage Gate

### 9.1 The Problem

A correctness bug was discovered where a client could lose rows during a
snapshot refresh. The scenario: a client has synced deltas from sites A, B, and
C, but a compaction only included A and B (site C's deltas had not reached the
compactor). If the client loads this manifest, it replaces its in-memory rows
with the segment state (losing C's contributions) and resets sync cursors to the
manifest watermarks (no watermark for C). With PN-Counters, the lost increments
from site C are permanently gone.

### 9.2 The Fix

Both `NodeCrdtClient` and `BrowserCrdtClient` now implement a
`manifestCoversKnownSites()` coverage gate that runs before applying any
manifest:

```typescript
// src/platform/node/nodeClient.ts:434-444
private manifestCoversKnownSites(manifest: ManifestFile): boolean {
  for (const [siteId, seq] of this.syncedSeqBySite.entries()) {
    if (seq <= 0) {
      continue;
    }
    if (!(siteId in manifest.sites_compacted)) {
      return false;
    }
  }
  return true;
}
```

The gate is checked early in `refreshFromSnapshotManifest()`:

```typescript
// src/platform/node/nodeClient.ts:388-392
if (!this.manifestCoversKnownSites(manifest)) {
  // Reject incomplete manifests for sites we already track; otherwise we may
  // replace rows with a partial snapshot and skip required log replay.
  return;
}
```

The logic: for every site the client has already synced deltas from (i.e.,
`syncedSeqBySite` has a positive seq), the manifest's `sites_compacted` must
contain that site. If any tracked site is missing from the manifest, the
manifest is silently skipped -- the client continues using its existing state
and delta-based sync until a future compaction produces a manifest that covers
all known sites.

The browser client has an identical implementation
(browserClient.ts:283-287, 321-331).

### 9.3 Why Sites with seq <= 0 Are Skipped

Sites with seq 0 are sites that the client knows about but has never
successfully synced any deltas from. They have contributed nothing to the
client's current state, so there is nothing to lose if the manifest omits them.

## 10. The Bloom Filter

Each segment includes a bloom filter over its primary keys, used to skip
segment scans for point lookups.

```typescript
// src/core/compaction.ts:199-224
export function buildBloomFilter(
  keys: SqlPrimaryKey[],
  bitsPerElement = 10,
): { bloom: Uint8Array; bloomK: number } {
  if (keys.length === 0) {
    return { bloom: new Uint8Array(0), bloomK: 0 };
  }

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

## 11. Concurrency and Safety

### 11.1 CAS on the Manifest

The manifest version acts as an optimistic lock. If two compaction jobs race:

1. Both read manifest version N.
2. Both build new segments and attempt to write manifest version N+1.
3. Only one CAS succeeds. The other sees `applied: false` and discards its work.

Orphaned segment files from the losing compaction are harmless -- they are never
referenced by any manifest.

### 11.2 Filesystem CAS with Lock File

The `FsSnapshotStore` (`src/platform/node/fsSnapshotStore.ts`) implements
manifest CAS using a filesystem lock file to serialize concurrent writers.

```typescript
// src/platform/node/fsSnapshotStore.ts:76-88
async putManifest(manifest: ManifestFile, expectedVersion: number): Promise<boolean> {
  assertManifestPublishable(manifest, expectedVersion);

  return this.withManifestLock(async () => {
    const priorManifest = await this.getManifest();
    const priorVersion = priorManifest?.version ?? 0;
    if (priorVersion !== expectedVersion) {
      return false;
    }
    await this.writeBytes(this.manifestPath, encodeBin(manifest));
    return true;
  });
}
```

The lock file mechanism (`withManifestLock()`, fsSnapshotStore.ts:148-157):

1. **Acquire lock:** Create `manifest.bin.lock` using `open(path, 'wx')` (the
   `wx` flag fails atomically with `EEXIST` if the file already exists). The
   PID and timestamp are written into the lock file.
2. **Execute CAS:** Inside the lock, re-read the manifest, compare versions,
   and write the new manifest if the version matches.
3. **Release lock:** Close the file handle and delete the lock file.

**Stale lock recovery** (fsSnapshotStore.ts:179-211): If a process crashes while
holding the lock, the lock file remains. The `tryClearStaleManifestLock()`
method reads the PID and timestamp from the lock file. If the lock is older than
30 seconds (`staleManifestLockMs`) and the owning process is no longer alive
(`process.kill(pid, 0)` fails), the lock file is removed.

**Atomic writes** (fsSnapshotStore.ts:127-138): All file writes use a
temp-file-then-rename pattern. The `writeBytes()` method writes to a temp file
(named with PID + timestamp + random suffix), then calls `rename()` which is
atomic on POSIX filesystems. Readers either see the old content or the new
content, never a partial write.

### 11.3 S3-Based CAS

**TigrisSnapshotStore** (`src/backend/tigrisSnapshotStore.ts`): Uses
S3 ETag-based conditional PUT (`IfMatch` / `IfNoneMatch`) for true CAS
semantics.

**HttpSnapshotStore** (`src/platform/node/httpSnapshotStore.ts`): Sends
`PUT /manifest?expect_version=N` and checks for HTTP 412 (Precondition Failed).

### 11.4 Contiguous Entry Safety

`takeContiguousEntriesSince()` (replication.ts) ensures the compactor
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

## 12. Testing Strategy

Compaction correctness is tested at five levels:

### 12.1 Lean Formal Proofs (Tier 4)

Machine-checked proofs in `lean/CrdtBase/Compaction/` that compaction preserves
state for all CRDT types, is idempotent, and that the snapshot cutover law holds.
These 10 theorems cover the abstract mathematical model.

### 12.2 Differential Random Testing (DRT)

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

### 12.3 Property-Based Tests

Several property test files cover compaction:

**`test/properties/compaction.prop.test.ts`** tests the full compaction pipeline
(including MessagePack encode/decode round-trip):

1. **Compaction preserves state**: Split ops at the midpoint, compact the prefix
   into a segment, encode/decode it, apply the suffix on top, and verify the
   result matches applying all ops directly.
2. **Compaction is idempotent**: Compact, encode, decode, re-compact, and verify
   the segment is identical.
3. **Rows are sorted**: Every segment has rows in primary key order.
4. **Bloom has no false negatives**: Every key in the segment is found by the
   bloom filter.

**`test/properties/compactionRetention.prop.test.ts`** validates TTL-based
pruning with two property-based tests (40 runs each):

1. **Row tombstone TTL** (line 38-54): Creates two deleted rows -- one older and
   one newer than the cutoff. After `pruneRuntimeRowsForCompaction()`, the old
   row is gone and the recent row survives.
2. **OR-Set tombstone TTL** (line 59-99): Creates an OR-Set with two tombstones
   straddling the cutoff. After pruning, only the newer tombstone remains.

**`test/properties/clientSnapshotPull.prop.test.ts`** validates the snapshot
cutover coverage gate and the full snapshot-first pull flow:

1. **Node client snapshot + delta equivalence** (line 215-266): Compact a prefix
   of events, create a node client that pulls from the compacted snapshot plus
   trailing deltas, verify it matches a client that replays all deltas directly.
2. **Browser client snapshot + delta equivalence** (line 268-312): Same for
   the browser client.
3. **Coverage gate rejection** (line 314-368): Forge a manifest missing a known
   site from `sites_compacted`, verify the node client rejects it and retains
   its prior state (line 362: `expect(after).toEqual(before)`).
4. **Browser coverage gate rejection** (line 370-419): Identical test for the
   browser client.
5. **Pending writes preservation** (line 421-464): Verify local unpushed writes
   survive a snapshot refresh.

**`test/properties/snapshotStore.prop.test.ts`** validates CAS atomicity and
encoding:

1. **Manifest/segment/schema encode/decode round-trips** (line 222-241).
2. **Manifest version CAS enforcement** (line 257-283): Seeds a filesystem
   store to a given version, then attempts CAS with various expected versions.
3. **Concurrent CAS atomicity** (line 285-318): Two `FsSnapshotStore` instances
   pointing at the same directory race to update the manifest. Exactly one wins
   (`expect(Number(appliedA) + Number(appliedB)).toBe(1)`).

### 12.4 End-to-End Tests

`test/e2e/three-clients.e2e.test.ts` and `test/e2e/s3-minio.e2e.test.ts` test
the full integration:

1. Three sites write data through a shared replicated log.
2. All three sites sync and converge to the same state.
3. Compaction runs, producing segments and a manifest.
4. A **fourth client** (`site-d`) that has never seen any deltas joins, pulls the
   manifest and segments, and verifies it gets the same query results.
5. A second compaction with no new deltas verifies idempotence (`opsRead === 0`).

### 12.5 Stress Tests

The stress test harness integrates compaction into its concurrent write
workload. One designated worker runs compaction every 30 operations, exercising
the interleaving of concurrent writes, delta replication, compaction, and
snapshot-based client bootstrapping under load.

## 13. Client-Side Segment Consumption

When a client calls `pull()`, `refreshFromSnapshotManifest()`
(nodeClient.ts:380-432) runs through the following steps:

1. **Skip if stale:** If the manifest is `null` or its version is not newer than
   `localSnapshotManifestVersion`, return early.
2. **Coverage gate:** Call `manifestCoversKnownSites()` -- reject manifests
   missing any tracked site (see Section 9).
3. **Load segments:** Download each segment, decode, and merge into a fresh
   `RuntimeRowState` map.
4. **Re-apply pending ops:** Iterate over `this.pendingOps` and call
   `applyCrdtOpToRows()` to preserve read-your-writes for unpushed local writes.
5. **Replace rows:** Clear the old row map and replace it with the new state.
6. **Reset cursors:** Set per-site sync cursors to compaction watermarks so
   subsequent delta pulls skip already-compacted entries.

The node client additionally caches downloaded segment files to disk in
`snapshotRootDir`. The browser client (browserClient.ts:275-319) follows the
same logic without filesystem caching.

## 14. Performance Implications and Tradeoffs

| Aspect | Without compaction | With compaction |
|---|---|---|
| New client bootstrap | Read all deltas (O(total ops)) | Read segments + recent deltas (O(rows + recent ops)) |
| Read path | Replay all deltas | Load segment + overlay recent deltas |
| Write path | Unchanged (always append delta) | Unchanged |
| Storage | Deltas only | Deltas + segments + old orphaned segments |
| Coordination | None | CAS on manifest only |
| Tombstone growth | Unbounded | Bounded by TTL (default 7 days) |

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

4. **TTL-based tombstone pruning:** OR-Set tombstones and deleted row tombstones
   are pruned after a configurable TTL (default 7 days). This bounds storage
   growth but introduces a correctness tradeoff: a site offline for longer than
   the TTL may produce add operations that are spuriously resurrected because
   the corresponding tombstone was already pruned. The 7-day default is a
   conservative choice that accommodates typical offline durations.

5. **Coverage gate conservatism:** The `manifestCoversKnownSites()` gate may
   cause a client to skip valid compaction manifests if the compactor has not
   yet seen deltas from a site the client has already synced. This is safe but
   can delay snapshot adoption. The client will adopt the manifest on a future
   pull once the compactor catches up.

## 15. Summary

Compaction in CRDTBase is a periodic batch job that folds accumulated delta
operations into pre-merged segment files, dramatically reducing the work needed
for new client bootstrap and query execution. Its correctness rests on 10
formally verified theorems (the fold-append law, per-CRDT specializations,
snapshot cutover law, and idempotence) that hold for all CRDT types. The
TTL-based tombstone garbage collection bounds storage growth while accepting a
practical tradeoff for very-long-offline sites. The filesystem CAS locking and
snapshot cutover coverage gate ensure durability and correctness under concurrent
compaction and mid-sync manifest updates. The design prioritizes simplicity and
debuggability -- single-level segments, no file deletion, MessagePack encoding
for universal inspectability -- making it an excellent learning implementation
of a storage engine compaction system.
