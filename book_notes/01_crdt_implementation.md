# Chapter 1: CRDT Implementation in CRDTBase

## Overview

CRDTBase implements four CRDT types -- LWW Register, PN-Counter, OR-Set, and MV-Register -- in TypeScript for runtime use and in Lean 4 for formal verification. The Lean model serves as both the mathematical specification and a test oracle via differential random testing (DRT). This chapter traces every definition, merge function, encoding, proof, and the correspondence between the two codebases.

---

## 1. Hybrid Logical Clock (HLC)

The HLC is the foundational ordering primitive. Every CRDT merge decision ultimately reduces to comparing HLC timestamps.

### 1.1 TypeScript HLC

**File:** `/home/kuitang/git/crdtbase/src/core/hlc.ts`

The HLC is a pair of `wallMs` (48-bit wall clock milliseconds) and `counter` (16-bit logical counter):

```typescript
// hlc.ts:1-4
export type Hlc = {
  wallMs: number;
  counter: number;
};
```

Packing into a single `bigint` for comparison (lines 14-19):

```typescript
// hlc.ts:14-19
export function packHlc(hlc: Hlc): bigint {
  if (hlc.wallMs >= WALL_MS_MAX || hlc.counter >= COUNTER_MAX) {
    throw new Error('HLC out of bounds');
  }
  return (BigInt(hlc.wallMs) << 16n) | BigInt(hlc.counter);
}
```

The total comparison function, with site-ID tiebreaking (lines 21-33):

```typescript
// hlc.ts:21-33
export function compareHlc(a: Hlc, b: Hlc): number {
  const packedA = packHlc(a);
  const packedB = packHlc(b);
  if (packedA === packedB) return 0;
  return packedA > packedB ? 1 : -1;
}

export function compareWithSite(a: Hlc, aSite: string, b: Hlc, bSite: string): number {
  const hlcCmp = compareHlc(a, b);
  if (hlcCmp !== 0) return hlcCmp;
  if (aSite === bSite) return 0;
  return aSite > bSite ? 1 : -1;
}
```

The `PersistedHlcFence` class (lines 41-64) enforces strict monotonicity of emitted HLCs across restarts:

```typescript
// hlc.ts:41-64
export class PersistedHlcFence {
  private highWater: Hlc | null;
  // ...
  commit(candidate: Hlc): void {
    this.assertNext(candidate);
    this.highWater = candidate;
  }
}
```

### 1.2 Lean HLC

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Hlc/Defs.lean`

The Lean HLC carries proof obligations in its fields (lines 16-21):

```lean
-- Hlc/Defs.lean:16-21
structure Hlc where
  wallMs : Nat
  counter : Nat
  wallMs_lt : wallMs < wallMsMax
  counter_lt : counter < counterMax
  deriving Repr, DecidableEq
```

This is a key difference from TypeScript: the Lean `Hlc` is a *dependent type* that can only be constructed with valid bounds proofs. The `mk?` smart constructor (lines 47-54) wraps the bounds check:

```lean
-- Hlc/Defs.lean:47-54
def mk? (wallMs counter : Nat) : Option Hlc :=
  if hWall : wallMs < wallMsMax then
    if hCounter : counter < counterMax then
      some { wallMs, counter, wallMs_lt := hWall, counter_lt := hCounter }
    else none
  else none
```

Packing uses multiplication instead of bit shift (semantically equivalent for Nat), line 26-27:

```lean
-- Hlc/Defs.lean:26-27
def pack (h : Hlc) : Nat :=
  h.wallMs * counterMax + h.counter
```

The extended comparison with site-ID tiebreak (lines 34-44):

```lean
-- Hlc/Defs.lean:34-44
def compareWithSite (a b : Hlc * String) : Ordering :=
  if _ : a.1.pack < b.1.pack then .lt
  else if _ : b.1.pack < a.1.pack then .gt
  else if _ : a.2 < b.2 then .lt
  else if _ : b.2 < a.2 then .gt
  else .eq
```

### 1.3 HLC Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Hlc/Props.lean`

Six key theorems are proved:

| Theorem | Line | Statement |
|---------|------|-----------|
| `recv_none_of_drift` | 10-15 | recv rejects timestamps drifting >60s into the future |
| `recv_some_bounds` | 18-24 | Successful recv output is within HLC bounds |
| `hlc_total_order` | 84-86 | Packed HLC values are totally ordered by `<` |
| `hlc_pack_preserves_order` | 89-105 | Higher wall clock always yields higher packed value |
| `hlc_counter_breaks_tie` | 108-122 | Equal wall clocks: packed order is exactly counter order |
| `hlc_now_monotonic` | 293-340 | `now()` strictly increases packed HLC |
| `hlc_recv_monotonic` | 352-460 | `recv()` output strictly exceeds both local and remote |

The `compareWithSite` ordering proofs (lines 124-280) establish it as a total order with swap and transitivity properties:

- `compareWithSite_self_eq` (line 132): reflexivity
- `compareWithSite_swap_lt` (line 226): if `a < b` then `b > a`
- `compareWithSite_swap_gt` (line 233): if `a > b` then `b < a`
- `compareWithSite_trans_lt` (line 260): transitivity of `<`
- `compareWithSite_trans_gt` (line 271): transitivity of `>`

These proofs are critical because the LWW merge theorems depend on them.

---

## 2. LWW Register

### 2.1 TypeScript Implementation

**File:** `/home/kuitang/git/crdtbase/src/core/crdt/lww.ts`

The LWW register is the simplest CRDT -- a single value tagged with an HLC and site ID:

```typescript
// lww.ts:3-7
export type LwwRegister<T> = {
  val: T;
  hlc: Hlc;
  site: string;
};
```

Merge logic (lines 23-30): compare `(hlc, site)` lexicographically; the greater one wins. On exact equality, return `a` (left-bias):

```typescript
// lww.ts:23-30
export function mergeLww<T>(a: LwwRegister<T>, b: LwwRegister<T>): LwwRegister<T> {
  assertLwwEventConsistency(a, b);
  const cmp = compareWithSite(a.hlc, a.site, b.hlc, b.site);
  if (cmp >= 0) {
    return a;
  }
  return b;
}
```

The event-consistency assertion (lines 17-21) throws if two registers with the same `(hlc, site)` carry different payloads:

```typescript
// lww.ts:17-21
export function assertLwwEventConsistency<T>(a: LwwRegister<T>, b: LwwRegister<T>): void {
  if (isConflictingLwwEvent(a, b)) {
    throw new Error('conflicting LWW event identity: same (hlc, site) with different payloads');
  }
}
```

### 2.2 LWW Conflict Guard

**File:** `/home/kuitang/git/crdtbase/src/core/crdt/lwwConflictGuard.ts`

A broader conflict guard that tracks `(table, key, col, site, hlc)` tuples and rejects duplicate event identities with different payloads (lines 29-43):

```typescript
// lwwConflictGuard.ts:29-43
export class LwwConflictGuard {
  private readonly seen = new Map<string, string>();

  observe(identity: LwwEventIdentity, value: unknown): void {
    const key = encodeIdentity(identity);
    const nextFingerprint = fingerprintValue(value);
    const priorFingerprint = this.seen.get(key);
    if (priorFingerprint !== undefined && priorFingerprint !== nextFingerprint) {
      throw new Error(
        `conflicting LWW payload for identity ${identity.table}.${identity.col} ...`
      );
    }
    this.seen.set(key, nextFingerprint);
  }
}
```

### 2.3 Lean LWW

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Lww/Defs.lean`

```lean
-- Lww/Defs.lean:8-12
structure LwwRegister (alpha : Type) where
  val  : alpha
  hlc  : Hlc
  site : String
  deriving Repr, DecidableEq
```

Merge (lines 17-18): identical semantics -- if `a < b`, take `b`; otherwise take `a`:

```lean
-- Lww/Defs.lean:17-18
def merge {alpha : Type} (a b : LwwRegister alpha) : LwwRegister alpha :=
  if Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .lt then b else a
```

### 2.4 LWW Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Lww/Props.lean`

The key concept is `LwwConsistentPair` (lines 11-12): equal `(hlc, site)` implies identical state:

```lean
-- Lww/Props.lean:11-12
def LwwConsistentPair {alpha : Type} (a b : LwwRegister alpha) : Prop :=
  Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = Ordering.eq -> a = b
```

Proved theorems:

| Theorem | Line | Property |
|---------|------|----------|
| `lww_equal_key_implies_equal_payload` | 15-19 | Same event identity implies same payload |
| `dedup_rejects_conflicting_same_key` | 22-27 | Conflicting payloads violate consistency |
| `lww_merge_comm_of_consistent` | 30-48 | Commutativity under event-consistency |
| `lww_merge_assoc_of_consistent` | 51-83 | Associativity under pairwise event-consistency |
| `lww_merge_idem` | 85-89 | Idempotency: `merge(a, a) = a` |
| `lww_merge_comm_global_of_consistent` | 92-96 | Globalized commutativity |
| `lww_merge_assoc_global_of_consistent` | 99-106 | Globalized associativity |

The commutativity proof (lines 30-48) case-splits on the three-way comparison: `.lt`, `.eq`, `.gt`. For `.lt`, the swap lemma `compareWithSite_swap_lt` proves the other direction is `.gt`. For `.eq`, the consistency invariant collapses `a = b`. For `.gt`, the swap lemma gives `.lt` in the opposite direction.

The associativity proof (lines 51-83) case-splits on all nine combinations of `hab`, `hbc`, and `hac`, using transitivity of `compareWithSite` to eliminate impossible cases.

---

## 3. PN-Counter

### 3.1 TypeScript Implementation

**File:** `/home/kuitang/git/crdtbase/src/core/crdt/pnCounter.ts`

Two maps from site IDs to counts:

```typescript
// pnCounter.ts:1-6
export type SiteCountMap = Record<string, number>;

export type PnCounter = {
  inc: SiteCountMap;
  dec: SiteCountMap;
};
```

Merge is pointwise max over both maps (lines 28-40):

```typescript
// pnCounter.ts:28-40
function mergeSiteCountMaps(a: SiteCountMap, b: SiteCountMap): SiteCountMap {
  const out: SiteCountMap = {};
  const keys = new Set([...Object.keys(a), ...Object.keys(b)]);
  for (const key of keys) {
    const left = a[key] ?? 0;
    const right = b[key] ?? 0;
    const merged = Math.max(left, right);
    if (merged !== 0) {
      out[key] = merged;
    }
  }
  return out;
}
```

The full merge (lines 49-56):

```typescript
// pnCounter.ts:49-56
export function mergePnCounter(a: PnCounter, b: PnCounter): PnCounter {
  const left = normalizePnCounter(a);
  const right = normalizePnCounter(b);
  return {
    inc: mergeSiteCountMaps(left.inc, right.inc),
    dec: mergeSiteCountMaps(left.dec, right.dec),
  };
}
```

Delta application adds an amount to the per-site counter (lines 58-74):

```typescript
// pnCounter.ts:58-74
export function applyPnCounterDelta(
  counter: PnCounter, site: string, direction: PnDirection, amount: number,
): PnCounter {
  // ...
  const target = direction === 'inc' ? normalized.inc : normalized.dec;
  const next = { ...target, [site]: (target[site] ?? 0) + amount };
  // ...
}
```

Value materialization (lines 76-81):

```typescript
// pnCounter.ts:76-81
export function pnCounterValue(counter: PnCounter): number {
  const normalized = normalizePnCounter(counter);
  const inc = Object.values(normalized.inc).reduce((sum, value) => sum + value, 0);
  const dec = Object.values(normalized.dec).reduce((sum, value) => sum + value, 0);
  return inc - dec;
}
```

### 3.2 Lean PN-Counter

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/PnCounter/Defs.lean`

The Lean model uses functions from `String -> Nat` instead of hash maps, which makes proofs cleaner:

```lean
-- PnCounter/Defs.lean:6-8
structure PnCounter where
  inc : String -> Nat
  dec : String -> Nat
```

Merge (lines 28-31):

```lean
-- PnCounter/Defs.lean:28-31
def merge (a b : PnCounter) : PnCounter :=
  { inc := fun site => max (a.inc site) (b.inc site)
    dec := fun site => max (a.dec site) (b.dec site) }
```

An extensionality theorem (lines 10-23) is provided for structural equality proofs.

### 3.3 PN-Counter Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/PnCounter/Props.lean`

All three semilattice properties proved in just 7 lines of tactic code each:

```lean
-- PnCounter/Props.lean:8-10
theorem pn_counter_merge_comm (a b : PnCounter) :
    PnCounter.merge a b = PnCounter.merge b a := by
  ext site <;> simp [PnCounter.merge, Nat.max_comm]
```

```lean
-- PnCounter/Props.lean:13-15
theorem pn_counter_merge_assoc (a b c : PnCounter) :
    PnCounter.merge (PnCounter.merge a b) c =
      PnCounter.merge a (PnCounter.merge b c) := by
  ext site <;> simp [PnCounter.merge, Nat.max_assoc]
```

```lean
-- PnCounter/Props.lean:18-20
theorem pn_counter_merge_idem (a : PnCounter) :
    PnCounter.merge a a = a := by
  ext site <;> simp [PnCounter.merge]
```

These are remarkably concise because pointwise max over `Nat` directly reduces to standard library lemmas about `Nat.max`.

### 3.4 TypeScript vs Lean Correspondence

| TypeScript | Lean |
|-----------|------|
| `Record<string, number>` | `String -> Nat` |
| `Math.max(left, right)` | `max (a.inc site) (b.inc site)` |
| Zero-elision normalization | Implicit (function returns 0 for unseen sites) |
| `applyPnCounterDelta` | Not modeled (ops are pre-merged in compaction model) |

---

## 4. OR-Set (Observed-Remove Set)

### 4.1 TypeScript Implementation

**File:** `/home/kuitang/git/crdtbase/src/core/crdt/orSet.ts`

Each element carries a unique add-tag `(addHlc, addSite)`:

```typescript
// orSet.ts:3-16
export type OrSetTag = { addHlc: Hlc; addSite: string; };
export type OrSetElement<T> = { val: T; tag: OrSetTag; };
export type OrSet<T> = {
  elements: Array<OrSetElement<T>>;
  tombstones: OrSetTag[];
};
```

Merge (lines 100-105): union both elements and tombstones, then canonicalize:

```typescript
// orSet.ts:100-105
export function mergeOrSet<T>(a: OrSet<T>, b: OrSet<T>): OrSet<T> {
  return canonicalizeOrSet({
    elements: [...a.elements, ...b.elements],
    tombstones: [...a.tombstones, ...b.tombstones],
  });
}
```

Canonicalization (lines 90-98): deduplicate both lists, filter out elements whose tags appear in tombstones:

```typescript
// orSet.ts:90-98
export function canonicalizeOrSet<T>(state: OrSet<T>): OrSet<T> {
  assertOrSetElementConsistency(state.elements);
  const tombstones = dedupeAndSortTags(state.tombstones);
  const tombstoneKeys = new Set(tombstones.map((tag) => tagKey(tag)));
  const elements = dedupeAndSortElements(state.elements).filter(
    (element) => !tombstoneKeys.has(tagKey(element.tag)),
  );
  return { elements, tombstones };
}
```

Tag keys are string-encoded as `"${wallMs}:${counter}:${site}"` for deduplication (line 27):

```typescript
// orSet.ts:26-28
function tagKey(tag: OrSetTag): string {
  return `${tag.addHlc.wallMs}:${tag.addHlc.counter}:${tag.addSite}`;
}
```

### 4.2 Lean OR-Set

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/OrSet/Defs.lean`

The Lean model uses `Finset` instead of arrays, which gives union, membership, and filter operations with built-in deduplication semantics:

```lean
-- OrSet/Defs.lean:8-23
structure OrSetTag (Hlc : Type) where
  addHlc  : Hlc
  addSite : String
  deriving Repr, DecidableEq

structure OrSetElem (alpha : Type) (Hlc : Type) where
  val : alpha
  tag : OrSetTag Hlc
  deriving Repr, DecidableEq

structure OrSet (alpha : Type) (Hlc : Type) where
  elements   : Finset (OrSetElem alpha Hlc)
  tombstones : Finset (OrSetTag Hlc)
```

Canonicalize and merge (lines 35-47):

```lean
-- OrSet/Defs.lean:35-47
def OrSet.canonicalize (s : OrSet alpha Hlc) : OrSet alpha Hlc :=
  { elements := s.elements.filter (fun e => e.tag notin s.tombstones)
    tombstones := s.tombstones }

def OrSet.merge (a b : OrSet alpha Hlc) : OrSet alpha Hlc :=
  OrSet.canonicalize {
    elements := a.elements cup b.elements
    tombstones := a.tombstones cup b.tombstones
  }
```

### 4.3 OR-Set Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/OrSet/Props.lean`

| Theorem | Line | Property |
|---------|------|----------|
| `or_set_canonicalize_idem` | 9-12 | Canonicalization is idempotent |
| `or_set_canonicalize_no_tombstoned_tags` | 15-19 | No tombstoned elements survive canonicalization |
| `or_set_canonicalize_preserves_visible_values` | 22-26 | Visible value semantics unchanged by re-canonicalization |
| `or_set_merge_comm` | 29-32 | Commutativity |
| `or_set_merge_assoc` | 35-44 | Associativity (uses `aesop` for complex Finset reasoning) |
| `or_set_merge_idem` | 47-59 | Idempotency (requires `hClean` precondition: no elements already tombstoned) |

The idempotency proof requires a precondition `hClean : forall x in a.elements, x.tag notin a.tombstones` because a non-canonical set (with tombstoned elements still present) would lose those elements on the first canonicalization.

### 4.4 TypeScript vs Lean Correspondence

| TypeScript | Lean |
|-----------|------|
| `Array<OrSetElement<T>>` | `Finset (OrSetElem alpha Hlc)` |
| `OrSetTag[]` (tombstones) | `Finset (OrSetTag Hlc)` |
| `dedupeAndSortElements` + `dedupeAndSortTags` | Implicit in `Finset` (no duplicates by construction) |
| `Set.has(tagKey(...))` | `e.tag notin s.tombstones` |
| `[...a, ...b]` concatenation | `a.elements cup b.elements` (Finset union) |

---

## 5. MV-Register (Multi-Value Register)

### 5.1 TypeScript Implementation

**File:** `/home/kuitang/git/crdtbase/src/core/crdt/mvRegister.ts`

The MV-Register keeps all concurrent values -- unlike LWW which picks a winner, MV-Register surfaces conflicts to the application:

```typescript
// mvRegister.ts:3-11
export type MvRegisterValue<T> = {
  val: T;
  hlc: Hlc;
  site: string;
};

export type MvRegister<T> = {
  values: Array<MvRegisterValue<T>>;
};
```

Merge (lines 84-88): concatenate and canonicalize (dedupe by event key, sort):

```typescript
// mvRegister.ts:84-88
export function mergeMvRegister<T>(a: MvRegister<T>, b: MvRegister<T>): MvRegister<T> {
  return canonicalizeMvRegister({
    values: [...a.values, ...b.values],
  });
}
```

Canonicalization (lines 77-82): assert consistency, dedupe by `(hlc, site)`, sort:

```typescript
// mvRegister.ts:77-82
export function canonicalizeMvRegister<T>(state: MvRegister<T>): MvRegister<T> {
  assertMvEventConsistency(state.values);
  const deduped = dedupeByEvent(state.values);
  const values = deduped.sort((left, right) =>
    compareKeys(entrySortKey(left), entrySortKey(right)));
  return { values };
}
```

### 5.2 Lean MV-Register

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/MvRegister/Defs.lean`

```lean
-- MvRegister/Defs.lean:9-17
structure MvValue (alpha : Type) where
  val  : alpha
  hlc  : Hlc
  site : String
  deriving Repr, DecidableEq

structure MvRegister (alpha : Type) where
  values : Finset (MvValue alpha)
```

Merge is simply set union (lines 29-31):

```lean
-- MvRegister/Defs.lean:29-31
def merge {alpha : Type} [DecidableEq alpha] (a b : MvRegister alpha) : MvRegister alpha :=
  { values := a.values cup b.values }
```

### 5.3 MV-Register Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/MvRegister/Props.lean`

All three semilattice properties (lines 8-25) follow directly from `Finset.union_comm`, `Finset.union_assoc`, and `Finset.union_self`:

```lean
-- MvRegister/Props.lean:8-11
theorem mv_register_merge_comm {alpha : Type} [DecidableEq alpha]
    (a b : MvRegister alpha) : MvRegister.merge a b = MvRegister.merge b a := by
  ext x
  simp [MvRegister.merge, Finset.union_comm]
```

---

## 6. Operation Encoding and the SQL Write Path

### 6.1 Encoded Operations

**File:** `/home/kuitang/git/crdtbase/src/core/sql.ts` (lines 1-80, partial)

Operations are tagged with CRDT type numbers (from SPEC.md, Section 7):

| Tag | CRDT Type | SQL Syntax |
|-----|-----------|------------|
| 1 | LWW Register | `LWW<T>`, bare `STRING`/`NUMBER`/`BOOLEAN` |
| 2 | PN-Counter | `COUNTER` |
| 3 | OR-Set | `SET<T>` |
| 4 | MV-Register | `REGISTER<T>` |

Each encoded op carries (from SPEC.md, Section 6.1):

```typescript
type EncodedOp = {
  tbl: string;     // table name
  key: SqlValue;   // primary key
  col: string;     // column name
  typ: number;     // CRDT type tag
  hlc: string;     // hex-encoded bigint HLC
  site: string;    // originating site
  val: SqlValue;   // payload (type-specific)
};
```

### 6.2 SQL to CRDT Op Translation

**File:** `/home/kuitang/git/crdtbase/src/core/sqlEval.ts`

The `applyCrdtOpToRows` function (lines 408-533) is the runtime merge dispatcher. It switches on `op.kind`:

- `row_exists`: LWW merge on the hidden `_exists` column (lines 421-437)
- `cell_lww`: LWW merge on a regular column (lines 439-458)
- `cell_counter`: `applyPnCounterDelta` with `op.d` (inc/dec) and `op.n` (amount) (lines 460-470)
- `cell_or_set_add`: `mergeOrSet` with a single-element set (lines 472-488)
- `cell_or_set_remove`: `mergeOrSet` with tombstone tags (lines 490-506)
- `cell_mv_register`: `mergeMvRegister` with a single value (lines 508-529)

### 6.3 Row Materialization

**File:** `/home/kuitang/git/crdtbase/src/core/sqlEval.ts` (lines 351-386)

Each CRDT state is projected to a plain value for SELECT queries:

```typescript
// sqlEval.ts:351-386
export function materializeRow(row: RuntimeRowState): Record<string, unknown> {
  for (const [column, state] of row.columns.entries()) {
    if (column === '_exists') continue;
    switch (state.typ) {
      case 1: values[column] = state.state.val; break;
      case 2: values[column] = pnCounterValue(state.state); break;
      case 3: /* distinct visible values */ break;
      case 4: /* single value or array of concurrent values */ break;
    }
  }
}
```

---

## 7. Table-Level CRDT Composition

### 7.1 Lean Table Model

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Table/Defs.lean`

A composite row bundles all four CRDT column types plus a row-visibility flag:

```lean
-- Table/Defs.lean:11-17
structure TableRowState (alpha beta gamma Hlc : Type) where
  alive : LwwRegister Bool
  lwwCol : LwwRegister alpha
  counterCol : PnCounter
  setCol : OrSet beta Hlc
  registerCol : MvRegister gamma
```

Row merge is componentwise (lines 19-27):

```lean
-- Table/Defs.lean:19-27
def mergeTableRow (a b : TableRowState alpha beta gamma Hlc) : TableRowState alpha beta gamma Hlc :=
  { alive := LwwRegister.merge a.alive b.alive
    lwwCol := LwwRegister.merge a.lwwCol b.lwwCol
    counterCol := PnCounter.merge a.counterCol b.counterCol
    setCol := OrSet.merge a.setCol b.setCol
    registerCol := MvRegister.merge a.registerCol b.registerCol }
```

Table-level merge is pointwise by key (lines 33-35):

```lean
-- Table/Defs.lean:33-35
def mergeTable (a b : TableState kappa alpha beta gamma Hlc) : TableState kappa alpha beta gamma Hlc :=
  fun key => mergeTableRow (a key) (b key)
```

### 7.2 Table Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Table/Props.lean`

Whole-table properties lift from row properties (lines 13-36):

- `table_merge_comm_of_row_comm` (line 13)
- `table_merge_assoc_of_row_assoc` (line 21)
- `table_merge_idem_of_row_idem` (line 30)

Operator composition properties (lines 39-99):

- `apply_counter_preserves_visibility` (line 44): Counter updates do not change `alive`
- `apply_set_preserves_visibility` (line 52): OR-Set updates do not change `alive`
- `apply_register_preserves_visibility` (line 62): MV-Register updates do not change `alive`
- `row_exists_counter_commute` (line 70): Row-existence and counter updates commute
- `row_exists_set_commute` (line 80): Row-existence and OR-Set updates commute
- `row_counter_register_commute` (line 91): Counter and MV-Register updates commute

Disjoint-key commutativity (lines 106-130):

```lean
-- Table/Props.lean:106-130
theorem modify_row_at_disjoint_commute
    (table : TableState kappa alpha beta gamma Hlc)
    (k1 k2 : kappa) (hNe : k1 <> k2)
    (f g : TableRowState alpha beta gamma Hlc -> TableRowState alpha beta gamma Hlc)
    : modifyRowAt (modifyRowAt table k1 f) k2 g =
      modifyRowAt (modifyRowAt table k2 g) k1 f
```

---

## 8. Tombstone (Delete) Model

### 8.1 Lean Tombstone

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Tombstone/Defs.lean`

Deletion is modeled as an LWW register over `Bool`:

```lean
-- Tombstone/Defs.lean:10
abbrev TombstoneState := LwwRegister Bool
```

- `deleteState hlc site` constructs `{ val := true, hlc, site }` (line 13)
- `liveState hlc site` constructs `{ val := false, hlc, site }` (line 19)
- `merge` is just `LwwRegister.merge` (line 25)

### 8.2 Tombstone Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Tombstone/Props.lean`

Three theorems (lines 11-36):

- `delete_wins_if_later`: A later delete tombstones the row
- `write_resurrects_if_later`: A later write un-tombstones the row
- `tombstone_stable_without_new_writes`: Repeated merge with self preserves state

---

## 9. Convergence Framework

### 9.1 Lean Convergence Definitions

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Convergence/Defs.lean`

```lean
-- Convergence/Defs.lean:10-11
def applyOps {sigma alpha : Type} (step : sigma -> alpha -> sigma) (init : sigma) (ops : List alpha) : sigma :=
  List.foldl step init ops
```

Two op streams are equivalent if they are permutations:

```lean
-- Convergence/Defs.lean:14-15
structure SameOps {alpha : Type} (ops1 ops2 : List alpha) : Prop where
  perm : List.Perm ops1 ops2
```

### 9.2 Convergence Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Convergence/Props.lean`

The abstract convergence theorem (lines 14-18):

```lean
-- Convergence/Props.lean:14-18
theorem convergence_of_perm {sigma alpha : Type}
    (step : sigma -> alpha -> sigma) [RightCommutative step]
    (init : sigma) {ops1 ops2 : List alpha} (hPerm : List.Perm ops1 ops2) :
    applyOps step init ops1 = applyOps step init ops2 := by
  simpa [applyOps] using (hPerm.foldl_eq (f := step) init)
```

This uses Lean 4's `List.Perm.foldl_eq` lemma: a `foldl` over a `RightCommutative` function is invariant under permutation.

The bridge theorem `convergence_of_comm_assoc` (lines 28-42) constructs a `RightCommutative` instance from raw commutativity and associativity proofs:

```lean
-- Convergence/Props.lean:28-42
theorem convergence_of_comm_assoc {alpha : Type}
    (merge : alpha -> alpha -> alpha)
    (hComm : forall a b, merge a b = merge b a)
    (hAssoc : forall a b c, merge (merge a b) c = merge a (merge b c))
    ...
    : applyOps merge init ops1 = applyOps merge init ops2 := by
  letI : RightCommutative merge := { right_comm := by
    intro a b c
    calc merge (merge a b) c = merge a (merge b c) := hAssoc a b c
      _ = merge a (merge c b) := by rw [hComm b c]
      _ = merge (merge a c) b := (hAssoc a c b).symm }
  exact convergence_of_perm merge init hPerm
```

Per-type convergence theorems are instantiated:

| Theorem | Line | CRDT Type |
|---------|------|-----------|
| `convergence_lww_of_consistent` | 108-115 | LWW under event-consistency |
| `convergence_pn_counter` | 127-130 | PN-Counter (unconditional) |
| `convergence_or_set` | 143-148 | OR-Set (unconditional) |
| `convergence_mv_register` | 163-168 | MV-Register (unconditional) |

Composite convergence for multi-column rows (lines 49-88):

```lean
-- Convergence/Props.lean:49-88
theorem convergence_composite
    (mergeA : alpha -> alpha -> alpha)
    (mergeB : beta -> beta -> beta)
    (hCommA hAssocA hCommB hAssocB ...)
    : applyOps (mergeComposite mergeA mergeB) init ops1 =
      applyOps (mergeComposite mergeA mergeB) init ops2
```

`Std.Commutative` and `Std.Associative` instances are registered for PN-Counter (lines 119-123), OR-Set (lines 136-139), and MV-Register (lines 156-159), enabling the generic `convergence_of_perm` path.

---

## 10. Compaction

### 10.1 Lean Compaction Model

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Compaction/Defs.lean`

Compaction is modeled as a split fold: apply the merge function to a prefix, then continue with the suffix:

```lean
-- Compaction/Defs.lean:13-15
def foldPrefixSuffix {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (ops : List alpha) (split : Nat) : beta :=
  List.foldl step (List.foldl step init (ops.take split)) (ops.drop split)
```

### 10.2 Compaction Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Compaction/Props.lean`

The central theorem (lines 10-25): split compaction equals a full fold:

```lean
-- Compaction/Props.lean:10-25
theorem foldPrefixSuffix_eq_foldl {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (ops : List alpha) (split : Nat) :
    foldPrefixSuffix step init ops split = List.foldl step init ops
```

The proof chains through `List.foldl_append` and `List.take_append_drop`.

Also proved:

- `compaction_preserves_state` (line 36): Folding a prefix then suffix equals folding the concatenation
- `compaction_idempotent` (line 48): Re-compacting with no new ops is a no-op
- Per-type compaction preservation for PN-Counter (line 55), OR-Set (line 67), MV-Register (line 80), and LWW (line 93)

### 10.3 TypeScript Compaction

**File:** `/home/kuitang/git/crdtbase/src/core/compaction.ts`

The TypeScript compaction module (414 lines) implements the practical segment-building pipeline:

1. `segmentFileToRuntimeRows` (line 235): Deserializes segment binary to runtime row state
2. `applyOpsToRuntimeRows` (line 226): Applies delta ops to runtime rows
3. `buildSegmentFile` (line 317): Sorts rows by PK, builds bloom filter, computes `hlc_max`
4. `buildSegmentsFromRows` (line 346): Groups rows by table and partition, builds segments
5. `buildManifestSegmentRef` (line 373): Creates manifest entries with key ranges and sizes

---

## 11. SQL Verification

### 11.1 Lean SQL Model

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Sql/Defs.lean`

The Lean SQL model (748 lines) covers:

- SQL AST types: `InsertStatement`, `UpdateStatement`, `CounterStatement`, `SetStatement`, `DeleteStatement`, `SelectStatement` (lines 105-174)
- Column CRDT type tags: `SqlColumnCrdt` (lines 189-195)
- Schema structures: `SqlColumnSchema`, `SqlTableSchema` (lines 216-251)
- `generateCrdtOpsCore` (line 646): The core write-path function that maps SQL statements to CRDT ops
- `buildSelectPlan` (line 720): The query planner that routes SELECTs to partitions

### 11.2 SQL Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Sql/Props.lean`

| Theorem | Line | Property |
|---------|------|----------|
| `write_ops_type_sound` | 60-73 | Generated ops always have valid CRDT type tags (1-4) |
| `write_ops_syncable` | 76-89 | Generated ops always have non-empty tbl, col, hlc, site |
| `no_nonsync_for_valid_crdt_writes` | 92-98 | Restatement as explicit field constraints |
| `planner_partition_default_route` | 100-103 | No partition config routes to `_default` |
| `planner_partition_sound` | 106-115 | Equality predicate routes to correct partition |
| `planner_partition_sound_all_partitions` | 117-124 | Empty WHERE routes to all partitions |
| `planner_partition_sound_all_partitions_of_no_match` | 127-132 | No matching predicate routes to all partitions |
| `planner_filter_preservation` | 135-143 | Partition predicate removed from residual filters |
| `planner_filter_preservation_no_partition` | 145-148 | No partition config preserves all filters |
| `planner_filter_preservation_all_partitions` | 151-156 | No match preserves all filters |

---

## 12. Differential Random Testing Bridge

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/DiffTest/Main.lean`

The DRT executable (910 lines) is a JSON Lines protocol server that handles commands:

| Command Type | Handler | Line |
|-------------|---------|------|
| `lww_merge` | `handleLwwMerge` | 307-314 |
| `pn_merge` | `handlePnMerge` | 336-345 |
| `or_set_merge` | `handleOrSetMerge` | 378-385 |
| `mv_merge` | `handleMvMerge` | 406-413 |
| `sql_generate_ops` | `handleSqlGenerateOps` | 834-837 |
| `sql_build_select_plan` | `handleSqlBuildSelectPlan` | 839-842 |
| `sql_eval` | `handleSqlEval` | 812-832 |
| `replication_list_sites` | `handleReplicationListSites` | 844-847 |
| `replication_get_head` | `handleReplicationGetHead` | 849-853 |
| `replication_read_since` | `handleReplicationReadSince` | 855-860 |

The main loop (lines 892-909) reads lines from stdin, dispatches to handlers, and writes JSON responses to stdout. This is consumed by the TypeScript test harness via child process IPC.

### 12.1 Replication Model

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Replication/Defs.lean`

The Lean replication model (62 lines) provides:

- `listSites`: Extract unique sorted site IDs from log entries
- `canonicalSeqs`: Extract sorted seq numbers for a site
- `getHead`: Get maximum seq for a site
- `readSince`: Return contiguous entries after a cursor position

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Replication/Props.lean`

The `readSince_mem_gt_since` theorem (line 26) proves that every entry returned by `readSince` has seq strictly greater than `since`.

---

## 13. Summary: How TypeScript and Lean Correspond

### 13.1 Architecture

```
TypeScript (runtime)          Lean (specification + proofs)
=====================         ==============================
src/core/hlc.ts          <->  lean/CrdtBase/Hlc/Defs.lean
src/core/crdt/lww.ts     <->  lean/CrdtBase/Crdt/Lww/Defs.lean
src/core/crdt/pnCounter.ts <-> lean/CrdtBase/Crdt/PnCounter/Defs.lean
src/core/crdt/orSet.ts   <->  lean/CrdtBase/Crdt/OrSet/Defs.lean
src/core/crdt/mvRegister.ts <-> lean/CrdtBase/Crdt/MvRegister/Defs.lean
src/core/sqlEval.ts      <->  lean/CrdtBase/DiffTest/Main.lean (evaluator)
src/core/sql.ts          <->  lean/CrdtBase/Sql/Defs.lean (planner + ops)
src/core/compaction.ts   <->  lean/CrdtBase/Compaction/Defs.lean
src/core/replication.ts  <->  lean/CrdtBase/Replication/Defs.lean
```

### 13.2 Design Differences

| Aspect | TypeScript | Lean |
|--------|-----------|------|
| Collections | `Array`, `Map`, `Record` | `Finset`, `List`, `String -> Nat` |
| HLC storage | `bigint` via bit shift | `Nat` via multiplication |
| Deduplication | Explicit `dedupeBy*` functions | Implicit in `Finset` |
| Bounds checking | Runtime `throw` | Dependent types (`wallMs_lt`, `counter_lt`) |
| Binary encoding | MessagePack via `@msgpack/msgpack` | Not modeled (out of proof scope) |
| Merge dispatch | `switch` on `op.kind` string | Pattern match on `SqlWriteStatement` |

### 13.3 Proof Inventory

| Tier | Count | Status |
|------|-------|--------|
| 1. CRDT Semilattice | 12 theorems | All proved |
| 2. HLC Ordering | 12 theorems | All proved |
| 3. Convergence | 5 theorems | All proved |
| 4. Compaction | 7 theorems | All proved |
| 5. Tombstone | 3 theorems | All proved |
| 6. Table Composition | 8 theorems | All proved |
| 7. SQL Soundness | 10 theorems | All proved |
| 8. Replication | 2 theorems | All proved |
| **Total** | **~59 theorems** | **All proved** |

### 13.4 The Verification-Guided Development Loop

1. Write Lean definitions (`Defs.lean`) as the specification
2. Write TypeScript implementation
3. Run DRT: TypeScript test harness generates random inputs, pipes through both Lean executable and TypeScript, compares outputs
4. Write Lean proofs (`Props.lean`) to establish mathematical guarantees
5. Any DRT divergence is a bug in one codebase -- fix and re-verify

This follows the Cedar verification methodology: the Lean model is the source of truth for *what* the system should do, while the TypeScript is the source of truth for *how* it runs in production.
