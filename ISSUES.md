# CRDTBase Issue Tracker

Extracted from book chapters 1--7. Prioritized by severity.

---

## P0 (Critical) -- Could cause silent data corruption or loss

### ~~P0-1: PN-Counter double-application on crash recovery~~ FIXED

**Status:** Fixed. `NodeCrdtClient` now commits local state via an atomic
`state_bundle.bin` write (temp file + `rename`), and startup prefers that
bundle over split legacy files. This prevents replaying already-applied
PN-counter deltas when legacy `sync.bin` is stale.

**Source:** Ch5 s5.8 Concern 1; Ch6 s6.6.4 Warning "PN-Counter Double-Application"

**Problem:** `applyPnCounterDelta` is additive, not idempotent. If the process
crashes between writing `state.bin` and `sync.bin`, counter ops in the most
recent batch will be replayed on restart, silently inflating the counter. Unlike
LWW/OR-Set/MV-Register (whose merges are idempotent), replaying a `+3` counter
op twice produces `+6`.

**Impact:** Silent data corruption -- the counter value becomes permanently
higher than the correct value, and no subsequent merge can correct it.

**Files:**
- `src/platform/node/nodeClient.ts` (persistStateFiles -- non-atomic writes)
- `src/core/crdt/pnCounter.ts` (applyPnCounterDelta)

**Fix type:** Code fix (atomic persistence or WAL)
**Complexity:** Significant

---

### ~~P0-2: Non-atomic local persistence (state.bin / pending.bin / sync.bin)~~ FIXED

**Status:** Fixed. Local persistence now uses an atomic bundle commit first,
then writes `state.bin`, `pending.bin`, and `sync.bin` as compatibility
artifacts. Correctness no longer depends on cross-file write ordering.

**Source:** Ch5 s5.8 Concern 5

**Problem:** The Node client writes `state.bin`, `pending.bin`, and `sync.bin`
via `Promise.all` -- no atomic transaction, no write-ahead log, no
`rename()` dance. A crash between writes leaves the three files inconsistent.

**Impact:** For LWW/OR-Set/MV-Register columns the worst case is redundant work.
For PN-Counter columns this directly triggers P0-1 (counter inflation).

**Files:**
- `src/platform/node/nodeClient.ts` (persistStateFiles, ~line 301-331)

**Fix type:** Code fix (write-ahead log, or atomic rename pattern)
**Complexity:** Moderate

---

### ~~P0-3: FsSnapshotStore CAS is not truly atomic~~ FIXED

**Status:** Fixed. `FsSnapshotStore.putManifest` now uses a filesystem lock
(`manifest.bin.lock`) to serialize CAS writers, and manifest writes are done
with temp-file + atomic `rename`.

**Source:** Ch6 s6.5 (CAS table)

**Problem:** The filesystem-based CAS in `FsSnapshotStore` uses a double-read
before writing. There is a race window between the reads and the write. If two
compactors run concurrently on the same filesystem, one could silently overwrite
the other's manifest, causing data loss (segment references lost).

**Impact:** Concurrent compaction on the same machine can corrupt the manifest
and permanently orphan segment data that was the latest compacted state.

**Files:**
- `src/platform/node/fsSnapshotStore.ts` (~line 53-71)

**Fix type:** Code fix (use `fs.rename` atomicity or file locking)
**Complexity:** Moderate

---

## P1 (High) -- Could cause incorrect behavior under specific conditions

### P1-1: Browser client does not persist HLC high-water mark

**Source:** Ch1 s5.4 Warning "Browser HLC Gap"; Ch5 s5.8 Concern 4

**Problem:** `BrowserCrdtClient` holds `lastLocalHlc` in memory only. A page
refresh within the same millisecond could reuse a `(wallMs, counter)` value.
If the same site ID produces two events with identical `(wallMs, counter)` but
different payloads, `assertLwwEventConsistency` will throw at merge time on
any replica that receives both.

**Impact:** Merge-time exceptions that halt replication for the affected row.
Under very tight timing, potential violation of the LWW total-order invariant.

**Files:**
- `src/platform/browser/browserClient.ts`

**Fix type:** Code fix (persist HLC to IndexedDB, localStorage, or OPFS)
**Complexity:** Moderate

---

### ~~P1-2: Composite row semilattice not directly proved end-to-end~~ FIXED

**Status:** Fixed in commit `27076be`. Added `ValidTableRowPair`/`Triple`
predicates and proved `mergeTableRow_comm_of_valid`, `mergeTableRow_assoc_of_valid`,
`mergeTableRow_idem_of_valid` directly under event-consistency, then lifted to
whole-table `mergeTable_*_of_valid` theorems.

**Source:** Ch3 s3.11 Warning "Verification Gaps" bullet 5

**Files:**
- `lean/CrdtBase/Crdt/Table/Props.lean`

---

### ~~P1-3: OR-Set idempotence precondition not formally chained~~ FIXED

**Status:** Fixed in commit `27076be`. Added `or_set_merge_canonicalized`
(merge output is always clean) and composed it into `or_set_merge_idem_general`
for precondition-free idempotence.

**Source:** Ch3 s3.11 Warning "Verification Gaps" bullet 6

**Files:**
- `lean/CrdtBase/Crdt/OrSet/Props.lean`

---

## P2 (Medium) -- Missing safety guardrails, incomplete proofs

### P2-1: OR-Set tombstone growth is unbounded

**Source:** Ch5 s5.8 Concern 2; Ch6 s6.9 Warning "Tombstone Retention Is Permanent"; Ch6 s6.11 Warning "Tradeoff 4"

**Problem:** OR-Set tombstones are never garbage-collected. Every `REMOVE`
operation adds tombstone tags that persist forever. The spec mentions a
compaction TTL for tombstone pruning (default: 7 days), but it is not
implemented.

**Impact:** Segment files grow monotonically. Query-time filtering pays
O(|tombstones|) per canonicalization. Workloads with high churn on set columns
degrade performance over time.

**Files:**
- `src/core/crdt/orSet.ts`
- `src/core/compaction.ts`
- `src/platform/node/compactor.ts`

**Fix type:** Code fix (implement TTL-based tombstone pruning during compaction)
**Complexity:** Significant

---

### P2-2: MV-Register never prunes dominated values

**Source:** Ch5 s5.8 Concern 3

**Problem:** `canonicalizeMvRegister` deduplicates by event identity
`(hlc, site)` but does not prune dominated values (where another value from the
same site has a strictly higher HLC). The register grows unboundedly with
concurrent writes from different sites.

**Impact:** MV-Register columns accumulate stale values over time, increasing
storage and serialization cost. Materialized query results may contain more
"concurrent" values than semantically necessary.

**Files:**
- `src/core/crdt/mvRegister.ts` (canonicalizeMvRegister)

**Fix type:** Code fix (prune values dominated by a newer write from the same site)
**Complexity:** Moderate

---

### P2-3: Row-level tombstone TTL not implemented

**Source:** Ch6 s6.9.2; Ch6 s6.11 Warning "Tradeoff 4"

**Problem:** The spec mentions TTL-based garbage collection of row tombstones
(default: 7 days), but the current compaction code does not implement this.
Deleted rows are retained in segment files indefinitely.

**Impact:** Storage waste -- deleted rows consume space forever. For workloads
with frequent delete/re-insert cycles, segment files grow without bound.

**Files:**
- `src/core/compaction.ts`
- `src/platform/node/compactor.ts`

**Fix type:** Code fix (filter tombstoned rows older than TTL during compaction)
**Complexity:** Moderate

---

### P2-4: TypeScript/Lean equivalence bridged only by testing, not formal refinement

**Source:** Ch3 s3.11 Warning "Verification Gaps" bullet 1

**Problem:** The Lean proofs verify the Lean specification, not the TypeScript
implementation. The bridge between the two codebases is differential random
testing (DRT), not formal refinement. A bug in TypeScript that DRT does not
exercise remains undetected.

**Impact:** The formal verification guarantee applies to the Lean model only.
TypeScript implementation correctness depends on DRT coverage, which is
statistical (100K+ samples) rather than exhaustive.

**Files:**
- `test/drt/*.drt.test.ts` (increase coverage)
- All `src/core/` files (correspondence to Lean)

**Fix type:** Design change (accept, or invest in formal refinement tooling)
**Complexity:** Significant

---

### P2-5: Network layer assumptions not formally modeled

**Source:** Ch3 s3.11 Warning "Verification Gaps" bullet 2

**Problem:** The proofs assume operations are eventually delivered. They do not
model message loss, duplication beyond CRDT idempotence, or Byzantine faults.

**Impact:** The convergence guarantee is conditional on the network eventually
delivering all deltas. Permanent message loss (e.g., S3 data loss) breaks
convergence.

**Files:**
- `lean/CrdtBase/Replication/Props.lean`

**Fix type:** Design change (document assumptions; S3 durability is 99.999999999%)
**Complexity:** Trivial (documentation) to Significant (formal model)

---

### P2-6: HLC real-time accuracy not formally modeled

**Source:** Ch3 s3.11 Warning "Verification Gaps" bullet 3

**Problem:** The proofs model HLC as bounded natural numbers. They do not prove
that JavaScript `Date.now()` is monotonic or that NTP keeps clocks within drift
bounds. Severe clock skew could cause unexpected LWW merge results (wrong
writer appears to "win").

**Impact:** Under extreme clock skew, LWW semantics may not match user intent
(a write with a lower real-world time could win due to a fast-running clock).

**Files:**
- `src/core/hlc.ts` (nextHlc uses Date.now())

**Fix type:** Code fix (add max-drift detection/rejection)
**Complexity:** Moderate

---

### P2-7: No orphaned segment file cleanup

**Source:** Ch6 s6.10 Note "Orphaned Segment Cleanup"

**Problem:** When a CAS-on-manifest fails, segment files written by the losing
compactor are orphaned -- never referenced by any manifest, never deleted.
Storage grows monotonically over time with each failed compaction attempt.

**Impact:** Storage waste proportional to the number of CAS failures times the
total dataset size.

**Files:**
- `src/platform/node/compactor.ts`
- `src/backend/tigrisSnapshotStore.ts`

**Fix type:** Code fix (add orphan-segment cleaner that diffs storage vs. manifest)
**Complexity:** Moderate

---

### P2-8: No old delta file cleanup

**Source:** Ch6 s6.9.3

**Problem:** Old delta files are never deleted from storage. After compaction
folds them into segments, they remain in S3 indefinitely. Clients never re-read
them, but they consume storage.

**Impact:** Storage cost grows without bound. Acceptable for small datasets but
problematic at scale.

**Files:**
- `src/platform/node/compactor.ts`
- `src/backend/tigrisReplicatedLog.ts`

**Fix type:** Code fix (delete deltas older than compaction watermark)
**Complexity:** Moderate

---

## P3 (Low) -- Nice-to-have improvements, cosmetic gaps

### P3-1: Full segment rewrite on every compaction

**Source:** Ch6 s6.11 Note "Tradeoff 1"

**Problem:** Every compaction rewrites all segments from scratch by reloading
prior segments plus new deltas. There is no incremental or partial compaction.
Cost is O(total_rows), not O(new_rows).

**Impact:** Compaction latency grows linearly with total dataset size. Acceptable
for learning-project scale but not for large datasets.

**Files:**
- `src/platform/node/compactor.ts`
- `src/core/compaction.ts`

**Fix type:** Design change (incremental/tiered compaction)
**Complexity:** Significant

---

### P3-2: Single-level segment architecture (no tiered compaction)

**Source:** Ch6 s6.11 Note "Tradeoff 2"

**Problem:** CRDTBase produces exactly one segment per (table, partition) pair.
No tiered compaction, no merge scheduling, no size-based triggers.

**Impact:** Every compaction processes the full dataset. Not a correctness issue
but limits scalability.

**Files:**
- `src/core/compaction.ts`

**Fix type:** Design change
**Complexity:** Significant

---

### P3-3: No schema evolution (ALTER TABLE)

**Source:** Ch1 s2 Non-goals; Ch5 s5.2

**Problem:** There is no `ALTER TABLE`. The only mutation is `DROP TABLE`. This
is listed as a non-goal but is a practical limitation.

**Impact:** Schema changes require creating a new table and migrating data.

**Files:**
- `src/core/sql.ts`

**Fix type:** Design change
**Complexity:** Significant

---

### P3-4: No multi-row transactions

**Source:** Ch1 s2 Non-goals

**Problem:** Listed as a non-goal. Each SQL statement is independent; there is
no way to atomically update multiple rows.

**Impact:** Applications requiring cross-row consistency must implement it at
the application layer.

**Files:**
- `src/core/sql.ts`
- `src/core/sqlEval.ts`

**Fix type:** Design change
**Complexity:** Significant

---

### P3-5: No foreign keys or referential integrity

**Source:** Ch1 s2 Non-goals

**Problem:** Listed as a non-goal. No enforcement of referential integrity
between tables.

**Impact:** Applications must enforce referential integrity at the application
layer.

**Files:**
- `src/core/sql.ts`

**Fix type:** Design change
**Complexity:** Significant

---

### P3-6: Browser client persistence is in-memory only

**Source:** Ch1 s3.2 (Platform Adapters table)

**Problem:** `BrowserCrdtClient` stores state in-memory only, lost on page
refresh. This is separate from the HLC persistence issue (P1-1) -- all row
state, pending ops, and sync cursors are lost.

**Impact:** Browser client is suitable for prototyping only, not production.

**Files:**
- `src/platform/browser/browserClient.ts`

**Fix type:** Code fix (persist to IndexedDB or OPFS)
**Complexity:** Moderate

---

### P3-7: Storage durability outside formal model

**Source:** Ch3 s3.11 Warning "Verification Gaps" bullet 4

**Problem:** Convergence assumes all operations survive storage. S3/Tigris
durability is outside the formal model.

**Impact:** Theoretical: if S3 loses an object, convergence breaks. Practical:
S3 durability is 99.999999999%, so this is negligible.

**Files:**
- (documentation only)

**Fix type:** Documentation
**Complexity:** Trivial

---

### P3-8: Binary encoding (MessagePack) not modeled in Lean

**Source:** Ch2 s2.10 (TypeScript/Lean correspondence table)

**Problem:** The MessagePack encode/decode layer is out of scope for Lean proofs.
A serialization bug could corrupt data without being detected by formal
verification.

**Impact:** Low -- DRT tests exercise the full encode/decode path, and
property-based round-trip tests provide high confidence.

**Files:**
- `src/core/encoding.ts`

**Fix type:** Design change (accept, covered by testing)
**Complexity:** Trivial (already mitigated)
