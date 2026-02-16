# Chapter 1: CRDT Implementation in CRDTBase

## Overview

CRDTBase implements four CRDT types -- LWW Register, PN-Counter, OR-Set, and MV-Register -- in TypeScript for runtime use and in Lean 4 for formal verification. The Lean model serves as both the mathematical specification and a test oracle via differential random testing (DRT). This chapter traces every definition, merge function, encoding, proof, and the correspondence between the two codebases.

---

## 1. Hybrid Logical Clock (HLC)

The HLC is the foundational ordering primitive. Every CRDT merge decision ultimately reduces to comparing HLC timestamps. The clock API was recently refactored around a factory-function design with standalone monotonic primitives and a persisted fence class for durability across restarts.

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

Bounds constants and the configurable drift limit (lines 6-14):

```typescript
// hlc.ts:6-14
const WALL_MS_MAX = 2 ** 48;
const COUNTER_MAX = 2 ** 16;
export const HLC_DRIFT_LIMIT_MS = 60_000;

export const HLC_LIMITS = {
  wallMsMax: WALL_MS_MAX,
  counterMax: COUNTER_MAX,
  driftLimitMs: HLC_DRIFT_LIMIT_MS,
};
```

The `assertHlcInBounds` helper (lines 34-45) validates both fields before any pack or emit operation:

```typescript
// hlc.ts:34-45
function assertHlcInBounds(hlc: Hlc): void {
  if (
    !Number.isInteger(hlc.wallMs) ||
    !Number.isInteger(hlc.counter) ||
    hlc.wallMs < 0 ||
    hlc.counter < 0 ||
    hlc.wallMs >= WALL_MS_MAX ||
    hlc.counter >= COUNTER_MAX
  ) {
    throw new Error('HLC out of bounds');
  }
}
```

Packing into a single `bigint` for comparison (lines 58-61):

```typescript
// hlc.ts:58-61
export function packHlc(hlc: Hlc): bigint {
  assertHlcInBounds(hlc);
  return (BigInt(hlc.wallMs) << 16n) | BigInt(hlc.counter);
}
```

The total comparison function, with site-ID tiebreaking (lines 63-75):

```typescript
// hlc.ts:63-75
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

#### 1.1.1 Drift Assertion

The `assertHlcDrift` function (lines 77-90) rejects HLCs that exceed a configurable drift limit (default 60 seconds) against the local wall clock. This is the primary defense against Byzantine clock skew:

```typescript
// hlc.ts:77-90
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

#### 1.1.2 Standalone Monotonic Primitives

The refactored API exposes two standalone functions rather than methods on a mutable clock object.

`nextMonotonicHlc` (lines 92-108) advances the local clock for a local event:

```typescript
// hlc.ts:92-108
export function nextMonotonicHlc(
  previous: Hlc | null,
  nowMs: number,
  driftLimitMs: number = HLC_DRIFT_LIMIT_MS,
): Hlc {
  const now = normalizeMs(nowMs, 'wall');
  const driftLimit = normalizeDriftLimitMs(driftLimitMs);
  if (previous !== null) {
    assertHlcDrift(previous, now, driftLimit);
  }
  const wallMs = previous === null ? now : Math.max(now, previous.wallMs);
  const counter = previous !== null && wallMs === previous.wallMs ? previous.counter + 1 : 0;
  const next = { wallMs, counter };
  assertHlcInBounds(next);
  assertHlcDrift(next, now, driftLimit);
  return next;
}
```

`recvMonotonicHlc` (lines 110-133) merges a remote HLC with the local state on receive:

```typescript
// hlc.ts:110-133
export function recvMonotonicHlc(
  local: Hlc | null,
  remote: Hlc,
  nowMs: number,
  driftLimitMs: number = HLC_DRIFT_LIMIT_MS,
): Hlc {
  const now = normalizeMs(nowMs, 'wall');
  const driftLimit = normalizeDriftLimitMs(driftLimitMs);
  assertHlcDrift(remote, now, driftLimit);
  const localHlc = local ?? { wallMs: 0, counter: 0 };
  assertHlcInBounds(localHlc);
  const wallMs = Math.max(localHlc.wallMs, remote.wallMs, now);
  let counter = 0;
  if (wallMs === localHlc.wallMs && wallMs === remote.wallMs) {
    counter = Math.max(localHlc.counter, remote.counter) + 1;
  } else if (wallMs === localHlc.wallMs) {
    counter = localHlc.counter + 1;
  } else if (wallMs === remote.wallMs) {
    counter = remote.counter + 1;
  }
  const received = { wallMs, counter };
  assertHlcInBounds(received);
  return received;
}
```

#### 1.1.3 Monotonic Wall Clock

`createMonotonicWallClock` (lines 135-163) produces a `() => number` function that uses `performance.now()` when available, falling back to `Date.now()` with a monotonic wrapper. The hybrid approach corrects for backward NTP jumps by anchoring to the monotonic offset and only ratcheting forward:

```typescript
// hlc.ts:135-163
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

#### 1.1.4 HlcClock Factory

The `createHlcClock` factory (lines 165-188) bundles the monotonic wall clock, drift limit, and the two core operations into a single `HlcClock` interface:

```typescript
// hlc.ts:165-188
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

#### 1.1.5 Strict Monotonicity Guard and Persisted Fence

`assertHlcStrictlyIncreases` (lines 190-194) throws if a candidate is not strictly greater than a previous HLC:

```typescript
// hlc.ts:190-194
export function assertHlcStrictlyIncreases(previous: Hlc | null, candidate: Hlc): void {
  if (previous !== null && compareHlc(candidate, previous) <= 0) {
    throw new Error('HLC monotonicity violation: candidate timestamp is not strictly greater');
  }
}
```

The `PersistedHlcFence` class (lines 196-219) enforces strict monotonicity of emitted HLCs across restarts. It persists a high-water mark that survives process boundaries:

```typescript
// hlc.ts:196-219
export class PersistedHlcFence {
  private highWater: Hlc | null;

  constructor(initial: Hlc | null = null) {
    this.highWater = initial;
  }

  loadPersisted(highWater: Hlc | null): void {
    this.highWater = highWater;
  }

  assertNext(candidate: Hlc): void {
    assertHlcStrictlyIncreases(this.highWater, candidate);
  }

  commit(candidate: Hlc): void {
    this.assertNext(candidate);
    this.highWater = candidate;
  }

  snapshot(): Hlc | null {
    return this.highWater;
  }
}
```

The four methods form a CAS-like protocol:
1. `loadPersisted()` -- restore high-water from durable storage on startup
2. `assertNext()` -- check a candidate without advancing state (for dry-run validation)
3. `commit()` -- atomically assert and advance the high-water
4. `snapshot()` -- read current high-water for durable persistence

### 1.2 Lean HLC

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Hlc/Defs.lean`

The Lean HLC carries proof obligations in its fields (lines 15-21):

```lean
-- Hlc/Defs.lean:15-21
/-- A bounded Hybrid Logical Clock timestamp. -/
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

Packing uses multiplication instead of bit shift (semantically equivalent for Nat), lines 26-27:

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

The `recv` function (lines 88-92) mirrors `recvMonotonicHlc` in TypeScript, rejecting drift violations and computing `max3` of the three wall clocks:

```lean
-- Hlc/Defs.lean:88-92
def recv (localHlc remote : Hlc) (now : Nat) : Option Hlc :=
  if _ : remote.wallMs > now + driftLimitMs then
    none
  else
    mk? (recvWall localHlc remote now) (recvCounter localHlc remote now)
```

### 1.3 HLC Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Hlc/Props.lean`

Twenty-one theorems are proved across 471 lines. The key theorems:

| Theorem | Line | Statement |
|---------|------|-----------|
| `recv_none_of_drift` | 10-15 | recv rejects timestamps drifting >60s into the future |
| `recv_some_bounds` | 18-24 | Successful recv output is within HLC bounds |
| `now_some_bounds` | 27-33 | Successful now output is within HLC bounds |
| `max3_ge_left/mid/right` | 36-45 | max3 dominates each argument |
| `recv_wallMs_monotonic` | 48-81 | recv output wallMs >= all three inputs |
| `hlc_total_order` | 84-86 | Packed HLC values are totally ordered by `<` |
| `hlc_pack_preserves_order` | 89-105 | Higher wall clock always yields higher packed value |
| `hlc_counter_breaks_tie` | 108-122 | Equal wall clocks: packed order is exactly counter order |
| `hlc_site_tiebreak_total` | 125-129 | Extended comparison covers all three Ordering constructors |
| `compareWithSite_self_eq` | 132-134 | Reflexivity |
| `compareWithSite_swap_lt` | 225-230 | If `a < b` then `b > a` |
| `compareWithSite_swap_gt` | 233-257 | If `a > b` then `b < a` |
| `compareWithSite_trans_lt` | 260-268 | Transitivity of `<` |
| `compareWithSite_trans_gt` | 271-279 | Transitivity of `>` |
| `pack_lt_of_same_wall_counter_lt` | 282-290 | Same wall: packed order = counter order |
| `hlc_now_monotonic` | 293-340 | `now()` strictly increases packed HLC |
| `hlc_now_strict_monotonic` | 343-349 | Alias for spec naming |
| `hlc_recv_monotonic` | 352-460 | `recv()` output strictly exceeds both local and remote |
| `hlc_recv_strict_monotonic` | 463-469 | Alias for spec naming |

The `compareWithSite` ordering proofs (lines 124-279) establish it as a total order with swap and transitivity properties. These are structured through a private `siteLexLt` predicate (line 136-137) that decomposes the comparison into a disjunction of "packed less" or "packed equal and site less", enabling clean transitivity via `siteLexLt_trans` (lines 178-194).

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
        `conflicting LWW payload for identity ${identity.table}.${identity.col} key=${identity.key} site=${identity.site}`,
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

Merge (lines 29-31):

```lean
-- PnCounter/Defs.lean:29-31
def merge (a b : PnCounter) : PnCounter :=
  { inc := fun site => max (a.inc site) (b.inc site)
    dec := fun site => max (a.dec site) (b.dec site) }
```

An extensionality theorem (lines 10-23) is provided for structural equality proofs.

### 3.3 PN-Counter Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/PnCounter/Props.lean`

All three semilattice properties proved in just one line of tactic code each:

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

Canonicalization (lines 90-98): assert element consistency, deduplicate both lists, filter out elements whose tags appear in tombstones:

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

Tag keys are string-encoded as `"${wallMs}:${counter}:${site}"` for deduplication (lines 26-28):

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
-- OrSet/Defs.lean:8-22
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
| `or_set_merge_canonicalized` | 62-67 | Merge output is always canonicalized |
| `or_set_merge_idem_general` | 71-74 | Precondition-free idempotence via chaining |

The idempotency proof (`or_set_merge_idem`, lines 47-59) requires a precondition `hClean : forall x in a.elements, x.tag notin a.tombstones` because a non-canonical set (with tombstoned elements still present) would lose those elements on the first canonicalization.

#### 4.3.1 Idempotence Chain (New)

The key insight for closing the OR-Set idempotence gap is a two-step chain:

1. `or_set_merge_canonicalized` (lines 62-67) proves that merge output is always clean -- every element in the result has its tag absent from tombstones:

```lean
-- OrSet/Props.lean:62-67
theorem or_set_merge_canonicalized {alpha Hlc : Type} [DecidableEq alpha] [DecidableEq Hlc]
    (a b : OrSet alpha Hlc) :
    forall x in (OrSet.merge a b).elements, x.tag notin (OrSet.merge a b).tombstones := by
  intro x hx
  simp [OrSet.merge] at hx |-
  exact hx.2
```

2. `or_set_merge_idem_general` (lines 71-74) chains the two, giving precondition-free idempotence for any `merge a b`:

```lean
-- OrSet/Props.lean:71-74
theorem or_set_merge_idem_general {alpha Hlc : Type} [DecidableEq alpha] [DecidableEq Hlc]
    (a b : OrSet alpha Hlc) :
    OrSet.merge (OrSet.merge a b) (OrSet.merge a b) = OrSet.merge a b := by
  exact or_set_merge_idem (OrSet.merge a b) (or_set_merge_canonicalized a b)
```

This eliminates the need for callers to track whether their OR-Set state is canonical, since any merge output is guaranteed to satisfy the idempotence precondition.

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

Merge (lines 102-106): concatenate and canonicalize:

```typescript
// mvRegister.ts:102-106
export function mergeMvRegister<T>(a: MvRegister<T>, b: MvRegister<T>): MvRegister<T> {
  return canonicalizeMvRegister({
    values: [...a.values, ...b.values],
  });
}
```

#### 5.1.1 MV-Register Canonicalization with Same-Site Pruning

Canonicalization (lines 94-100) now includes a critical pruning step that drops dominated values from the same site. This is the `pruneDominatedBySameSite` function (lines 77-92):

```typescript
// mvRegister.ts:77-92
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
    if (!max) {
      return true;
    }
    return compareHlc(entry.hlc, max) === 0;
  });
}
```

The full canonicalization pipeline (lines 94-100):

```typescript
// mvRegister.ts:94-100
export function canonicalizeMvRegister<T>(state: MvRegister<T>): MvRegister<T> {
  assertMvEventConsistency(state.values);
  const deduped = dedupeByEvent(state.values);
  const undominated = pruneDominatedBySameSite(deduped);
  const values = undominated.sort((left, right) =>
    compareKeys(entrySortKey(left), entrySortKey(right)));
  return { values };
}
```

The three-step canonicalization pipeline:
1. **Assert consistency** -- reject conflicting payloads for the same `(hlc, site)` event
2. **Dedupe by event** -- collapse identical event keys to a single entry
3. **Prune dominated** -- for each site, keep only the value with the newest HLC; older entries from the same site are superseded (not concurrent)

This pruning step is essential for correct multi-value semantics: if site A writes `v1` at `t=10` then `v2` at `t=20`, only `v2` should appear in the register, because `v1` was causally superseded. Without pruning, merge would accumulate stale entries from the same site.

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

Note that the Lean model does not include the `pruneDominatedBySameSite` step -- the Lean `MvRegister` is a pure semilattice over `Finset` union. The same-site pruning is a *runtime optimization* in TypeScript that reduces the number of concurrent values surfaced to the application. The DRT harness accounts for this difference by normalizing both outputs before comparison.

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

```lean
-- MvRegister/Props.lean:14-18
theorem mv_register_merge_assoc {alpha : Type} [DecidableEq alpha]
    (a b c : MvRegister alpha) :
    MvRegister.merge (MvRegister.merge a b) c = MvRegister.merge a (MvRegister.merge b c) := by
  ext x
  simp [MvRegister.merge, Finset.union_assoc]
```

```lean
-- MvRegister/Props.lean:21-24
theorem mv_register_merge_idem {alpha : Type} [DecidableEq alpha]
    (a : MvRegister alpha) : MvRegister.merge a a = a := by
  ext x
  simp [MvRegister.merge]
```

---

## 6. Operation Encoding and the SQL Write Path

### 6.1 Encoded Operations

**File:** `/home/kuitang/git/crdtbase/src/core/sql.ts`

Operations are tagged with CRDT type kinds (lines 148-197):

| Kind | CRDT Type | SQL Syntax |
|------|-----------|------------|
| `row_exists` | LWW Register (Bool) | INSERT/DELETE (hidden `_exists` column) |
| `cell_lww` | LWW Register | `LWW<T>`, bare `STRING`/`NUMBER`/`BOOLEAN` |
| `cell_counter` | PN-Counter | `COUNTER` |
| `cell_or_set_add` | OR-Set (add) | `SET<T>` |
| `cell_or_set_remove` | OR-Set (remove) | `SET<T>` |
| `cell_mv_register` | MV-Register | `REGISTER<T>` |

Each encoded op carries a `BaseCrdtOp` (lines 148-153):

```typescript
// sql.ts:148-153
type BaseCrdtOp = {
  tbl: string;
  key: SqlPrimaryKey;
  hlc: string;
  site: string;
};
```

The discriminated union `EncodedCrdtOp` (lines 191-197) covers all six op kinds, each extending `BaseCrdtOp` with kind-specific fields.

### 6.2 Schema System (DDL)

**File:** `/home/kuitang/git/crdtbase/src/core/sql.ts` (lines 26-42, 245-268)

CRDTBase now supports DDL statements that are themselves CRDT-replicated:

```typescript
// sql.ts:26-36
export type CreateTableStatement = {
  kind: 'create_table';
  table: string;
  columns: SqlCreateColumn[];
  partitionBy?: string;
};

export type DropTableStatement = {
  kind: 'drop_table';
  table: string;
};
```

```typescript
// sql.ts:38-42
export type AlterTableAddColumnStatement = {
  kind: 'alter_table_add_column';
  table: string;
  column: SqlCreateColumn;
};
```

Schema is stored as CRDT columns in `information_schema` tables (lines 245-268):

```typescript
// sql.ts:245-268
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

This design means `CREATE TABLE` generates CRDT ops for `information_schema.tables` (one row per table with pk_column and partition_by) and `information_schema.columns` (one row per column with table_name, column_name, crdt_kind). Schema changes are replicated exactly like data changes -- they merge via LWW on each metadata column, converging across sites without any special coordination protocol.

`ALTER TABLE ADD COLUMN` adds a new row to `information_schema.columns`. `DROP TABLE` tombstones the row in `information_schema.tables` by setting `_exists = false`.

### 6.3 SQL to CRDT Op Translation

**File:** `/home/kuitang/git/crdtbase/src/core/sqlEval.ts`

The `applyCrdtOpToRows` function is the runtime merge dispatcher. It switches on `op.kind`:

- `row_exists`: LWW merge on the hidden `_exists` column
- `cell_lww`: LWW merge on a regular column
- `cell_counter`: `applyPnCounterDelta` with `op.d` (inc/dec) and `op.n` (amount)
- `cell_or_set_add`: `mergeOrSet` with a single-element set
- `cell_or_set_remove`: `mergeOrSet` with tombstone tags
- `cell_mv_register`: `mergeMvRegister` with a single value

### 6.4 Row Materialization

**File:** `/home/kuitang/git/crdtbase/src/core/sqlEval.ts`

Each CRDT state is projected to a plain value for SELECT queries:

- **LWW** (tag 1): `state.val` directly
- **PN-Counter** (tag 2): `pnCounterValue(state)` = sum(inc) - sum(dec)
- **OR-Set** (tag 3): distinct visible values (elements not in tombstones)
- **MV-Register** (tag 4): single value or array of concurrent values

---

## 7. Table-Level CRDT Composition

### 7.1 Lean Table Model

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Table/Defs.lean`

A composite row bundles all four CRDT column types plus a row-visibility flag:

```lean
-- Table/Defs.lean:11-16
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

Row-level operations are defined as field-specific updates (lines 42-69): `applyRowExists`, `applyLwwCell`, `applyCounterCell`, `applySetCell`, `applyRegisterCell`. The `modifyRowAt` function (lines 72-77) lifts row operations to whole-table operations at a specific key.

### 7.2 Table Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Table/Props.lean`

This is the largest proof file, with 16 theorems across 254 lines. The proofs are organized into four layers.

#### Layer 1: Generic Lifting (lines 17-39)

Whole-table properties lift from row properties:

- `table_merge_comm_of_row_comm` (line 17): if row merge commutes, table merge commutes
- `table_merge_assoc_of_row_assoc` (line 25): if row merge associates, table merge associates
- `table_merge_idem_of_row_idem` (line 34): if row merge is idempotent, table merge is idempotent

All three are one-liners: `funext key` then apply the row hypothesis.

#### Layer 2: Validity Predicates and Instantiated Row Theorems (lines 43-155)

The `ValidTableRowPair` structure (lines 58-62) captures the system-level invariant:

```lean
-- Table/Props.lean:58-62
structure ValidTableRowPair (a b : TableRowState alpha beta gamma Hlc) : Prop where
  alive_consistent   : LwwConsistentPair a.alive b.alive
  lwwCol_consistent  : LwwConsistentPair a.lwwCol b.lwwCol
  setCol_a_clean     : forall x in a.setCol.elements, x.tag notin a.setCol.tombstones
  setCol_b_clean     : forall x in b.setCol.elements, x.tag notin b.setCol.tombstones
```

This bundles two requirements:
1. LWW event-consistency for the `alive` and `lwwCol` columns
2. OR-Set canonicalization (no element tag appears in tombstones)

Instantiated row theorems:

| Theorem | Line | Property |
|---------|------|----------|
| `mergeTableRow_comm_of_valid` | 66-75 | Row commutativity under validity predicate |
| `mergeTableRow_assoc_of_valid` | 86-97 | Row associativity under `ValidTableRowTriple` |
| `mergeTableRow_idem_of_valid` | 105-115 | Row idempotence under OR-Set canonicalization |

The `ValidTableRowTriple` structure (lines 79-83) requires pairwise LWW consistency for `(a,b)` and `(b,c)`:

```lean
-- Table/Props.lean:79-83
structure ValidTableRowTriple (a b c : TableRowState alpha beta gamma Hlc) : Prop where
  alive_ab : LwwConsistentPair a.alive b.alive
  alive_bc : LwwConsistentPair b.alive c.alive
  lww_ab   : LwwConsistentPair a.lwwCol b.lwwCol
  lww_bc   : LwwConsistentPair b.lwwCol c.lwwCol
```

Lifted whole-table theorems (lines 117-154):

| Theorem | Line | Property |
|---------|------|----------|
| `mergeTable_comm_of_valid` | 125-130 | Whole-table commutativity under `ValidTableState` |
| `mergeTable_assoc_of_valid` | 137-142 | Whole-table associativity under `ValidTableStateTriple` |
| `mergeTable_idem_of_valid` | 149-154 | Whole-table idempotence under `ValidTableStateIdem` |

#### Layer 3: Operator Composition (lines 158-250)

Visibility preservation theorems -- column updates to non-`alive` columns do not change row visibility:

| Theorem | Line | Property |
|---------|------|----------|
| `apply_counter_preserves_visibility` | 163-168 | Counter updates preserve `alive` |
| `apply_set_preserves_visibility` | 171-177 | OR-Set updates preserve `alive` |
| `apply_register_preserves_visibility` | 180-186 | MV-Register updates preserve `alive` |

Column commutativity theorems -- updates to independent columns commute:

| Theorem | Line | Property |
|---------|------|----------|
| `row_exists_counter_commute` | 189-196 | Row-existence and counter updates commute |
| `row_exists_set_commute` | 199-207 | Row-existence and OR-Set updates commute |
| `row_counter_register_commute` | 210-218 | Counter and MV-Register updates commute |

All six are proved by `cases row; rfl` -- the structure decomposition makes independence obvious.

#### Layer 4: Disjoint-Key Commutativity (lines 220-250)

```lean
-- Table/Props.lean:225-248
theorem modify_row_at_disjoint_commute
    (table : TableState kappa alpha beta gamma Hlc)
    (k1 k2 : kappa) (hNe : k1 <> k2)
    (f g : TableRowState alpha beta gamma Hlc -> TableRowState alpha beta gamma Hlc)
    : modifyRowAt (modifyRowAt table k1 f) k2 g =
      modifyRowAt (modifyRowAt table k2 g) k1 f
```

This proves that updates to different primary keys always commute, regardless of the column CRDT type. The proof works by `funext` then case-splitting on whether the current key equals `k1`, `k2`, or neither.

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
- `isDeleted` materializes the deletion bit (line 28)

### 8.2 Tombstone Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Tombstone/Props.lean`

Three theorems (lines 11-36):

- `delete_wins_if_later` (line 11): A later delete tombstones the row
- `write_resurrects_if_later` (line 20): A later write un-tombstones the row
- `tombstone_stable_without_new_writes` (line 29): Repeated merge with self preserves state

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

Nine theorems are proved across 174 lines:

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

Per-type convergence theorems:

| Theorem | Line | CRDT Type |
|---------|------|-----------|
| `convergence_lww` | 97-105 | LWW given explicit comm/assoc |
| `convergence_lww_of_consistent` | 108-115 | LWW under event-consistency |
| `convergence_pn_counter` | 126-130 | PN-Counter (unconditional) |
| `convergence_or_set` | 143-148 | OR-Set (unconditional) |
| `convergence_mv_register` | 163-168 | MV-Register (unconditional) |

`Std.Commutative` and `Std.Associative` instances are registered for PN-Counter (lines 119-123), OR-Set (lines 136-140), and MV-Register (lines 156-160), enabling the generic `convergence_of_perm` path.

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

Empty states for each CRDT type are defined (lines 18-29): `pnCounterEmpty`, `orSetEmpty`, `mvRegisterEmpty`, and an `lwwStep` function that handles `Option` for empty LWW base.

### 10.2 Compaction Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Compaction/Props.lean`

Ten theorems are proved across 119 lines:

| Theorem | Line | Property |
|---------|------|----------|
| `foldPrefixSuffix_eq_foldl` | 10-25 | Split compaction equals full fold |
| `foldPrefixSuffix_eq_foldl_all` | 28-32 | Same law for all split points |
| `compaction_preserves_state` | 36-45 | Prefix fold + suffix fold = concatenation fold |
| `compaction_idempotent` | 48-52 | Re-compacting with no new ops is a no-op |
| `pn_counter_compaction_preserves_state` | 55-64 | PN-Counter specialization |
| `or_set_compaction_preserves_state` | 67-77 | OR-Set specialization |
| `mv_register_compaction_preserves_state` | 80-90 | MV-Register specialization |
| `lww_compaction_preserves_state` | 93-102 | LWW specialization |
| `snapshot_then_suffix_replay_eq_full_fold` | 105-109 | Snapshot cutover law |
| `snapshot_cutover_idempotent_without_new_suffix` | 112-116 | Empty-suffix cutover is no-op |

The central theorem `foldPrefixSuffix_eq_foldl` (lines 10-25) chains through `List.foldl_append` and `List.take_append_drop`:

```lean
-- Compaction/Props.lean:10-25
theorem foldPrefixSuffix_eq_foldl {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (ops : List alpha) (split : Nat) :
    foldPrefixSuffix step init ops split = List.foldl step init ops
```

#### 10.2.1 Snapshot Cutover Proofs (New)

The snapshot cutover theorems formalize the correctness of loading a compacted state snapshot and replaying only new deltas:

```lean
-- Compaction/Props.lean:105-109
theorem snapshot_then_suffix_replay_eq_full_fold {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (compactedPrefix suffix : List alpha) :
    List.foldl step (List.foldl step init compactedPrefix) suffix =
      List.foldl step init (compactedPrefix ++ suffix) := by
  simpa using compaction_preserves_state step init compactedPrefix suffix
```

```lean
-- Compaction/Props.lean:112-116
theorem snapshot_cutover_idempotent_without_new_suffix {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (compactedPrefix : List alpha) :
    List.foldl step (List.foldl step init compactedPrefix) [] =
      List.foldl step init compactedPrefix := by
  simp
```

These two theorems together guarantee that a node joining the cluster can load a snapshot of the compacted prefix state, then replay only the suffix of ops that arrived after the snapshot, and arrive at the same state as if it had replayed the entire history from scratch.

### 10.3 TypeScript Compaction

**File:** `/home/kuitang/git/crdtbase/src/core/compaction.ts`

The TypeScript compaction module implements the practical segment-building pipeline:

1. `segmentFileToRuntimeRows`: Deserializes segment binary to runtime row state
2. `applyOpsToRuntimeRows`: Applies delta ops to runtime rows
3. `buildSegmentFile`: Sorts rows by PK, builds bloom filter, computes `hlc_max`
4. `buildSegmentsFromRows`: Groups rows by table and partition, builds segments
5. `buildManifestSegmentRef`: Creates manifest entries with key ranges and sizes

#### 10.3.1 Compaction Retention Policy (New)

TTL-based tombstone garbage collection is configured via `CompactionRetentionPolicy` (lines 54-61):

```typescript
// compaction.ts:54-61
export const DEFAULT_OR_SET_TOMBSTONE_TTL_MS = 7 * 24 * 60 * 60 * 1000;  // 7 days
export const DEFAULT_ROW_TOMBSTONE_TTL_MS = 7 * 24 * 60 * 60 * 1000;     // 7 days

export type CompactionRetentionPolicy = {
  nowMs: number;
  orSetTombstoneTtlMs: number;
  rowTombstoneTtlMs: number;
};
```

The `pruneRuntimeRowsForCompaction` function (lines 423-464) applies the retention policy:

```typescript
// compaction.ts:423-464
export function pruneRuntimeRowsForCompaction(
  rows: Map<string, RuntimeRowState>,
  policy: CompactionRetentionPolicy,
): void {
  const orSetCutoffMs = policy.nowMs - policy.orSetTombstoneTtlMs;
  const rowCutoffMs = policy.nowMs - policy.rowTombstoneTtlMs;

  for (const [storageKey, row] of [...rows.entries()]) {
    // Prune entire row if deleted and tombstone is expired
    const exists = row.columns.get('_exists');
    if (
      exists?.typ === 1 &&
      exists.state.val === false &&
      isHlcExpired(exists.state.hlc.wallMs, rowCutoffMs)
    ) {
      rows.delete(storageKey);
      continue;
    }

    // Prune expired OR-Set tombstones within surviving rows
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
  }
}
```

Two kinds of GC are applied:
1. **Row tombstone GC**: If `_exists = false` and the delete timestamp is older than `rowTombstoneTtlMs` (default 7 days), the entire row is pruned
2. **OR-Set tombstone GC**: Within surviving rows, OR-Set tombstones older than `orSetTombstoneTtlMs` are dropped, then the set is re-canonicalized

---

## 11. SQL Verification

### 11.1 Lean SQL Model

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Sql/Defs.lean`

The Lean SQL model covers:

- SQL AST types: `InsertStatement`, `UpdateStatement`, `CounterStatement`, `SetStatement`, `DeleteStatement`, `SelectStatement`
- Column CRDT type tags: `SqlColumnCrdt`
- Schema structures: `SqlColumnSchema`, `SqlTableSchema`
- `generateCrdtOpsCore`: The core write-path function that maps SQL statements to CRDT ops
- `buildSelectPlan`: The query planner that routes SELECTs to partitions

### 11.2 SQL Proofs

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Sql/Props.lean`

Ten theorems are proved across 158 lines, organized into two groups:

**Write-path soundness (lines 60-98):**

| Theorem | Line | Property |
|---------|------|----------|
| `write_ops_type_sound` | 60-73 | Generated ops always have valid CRDT type tags |
| `write_ops_syncable` | 76-89 | Generated ops always have non-empty tbl, col, hlc, site |
| `no_nonsync_for_valid_crdt_writes` | 92-98 | Restatement as explicit field constraints |

These are proved by unfolding `generateCrdtOps` into `generateCrdtOpsCore` followed by `validateGeneratedOps`, then applying helper lemmas that bridge the boolean validation functions (`generatedOpsHaveValidTagsB`, `generatedOpsAreSyncableB`) to their propositional counterparts.

**Read-path soundness (lines 100-156):**

| Theorem | Line | Property |
|---------|------|----------|
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

The DRT executable is a JSON Lines protocol server that handles commands:

| Command Type | Handler |
|-------------|---------|
| `lww_merge` | `handleLwwMerge` |
| `pn_merge` | `handlePnMerge` |
| `or_set_merge` | `handleOrSetMerge` |
| `mv_merge` | `handleMvMerge` |
| `sql_generate_ops` | `handleSqlGenerateOps` |
| `sql_build_select_plan` | `handleSqlBuildSelectPlan` |
| `sql_eval` | `handleSqlEval` |
| `replication_list_sites` | `handleReplicationListSites` |
| `replication_get_head` | `handleReplicationGetHead` |
| `replication_read_since` | `handleReplicationReadSince` |

The main loop reads lines from stdin, dispatches to handlers, and writes JSON responses to stdout. This is consumed by the TypeScript test harness via child process IPC.

### 12.1 Replication Model

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Replication/Defs.lean`

The Lean replication model provides:

- `listSites`: Extract unique sorted site IDs from log entries
- `canonicalSeqs`: Extract sorted seq numbers for a site
- `getHead`: Get maximum seq for a site
- `readSince`: Return contiguous entries after a cursor position

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Replication/Props.lean`

Four theorems are proved (lines 9-58):

| Theorem | Line | Property |
|---------|------|----------|
| `mem_takeContiguousFrom_mem` | 9-24 | Membership preservation through contiguous take |
| `readSince_mem_gt_since` | 26-42 | Every entry from `readSince` has seq > since |
| `readSince_after_watermark_only_returns_gt_watermark` | 45-49 | Watermark alias |
| `readSince_compacted_prefix_exclusion` | 52-58 | Entries at or below watermark are never replayed |

The `readSince_compacted_prefix_exclusion` theorem (lines 52-58) is particularly important for compaction correctness: it guarantees that once a compaction watermark is established, no stale entries will be replayed during replication.

---

## 13. Summary: How TypeScript and Lean Correspond

### 13.1 Architecture

```
TypeScript (runtime)              Lean (specification + proofs)
=====================             ==============================
src/core/hlc.ts              <->  lean/CrdtBase/Hlc/Defs.lean
src/core/crdt/lww.ts         <->  lean/CrdtBase/Crdt/Lww/Defs.lean
src/core/crdt/pnCounter.ts   <->  lean/CrdtBase/Crdt/PnCounter/Defs.lean
src/core/crdt/orSet.ts       <->  lean/CrdtBase/Crdt/OrSet/Defs.lean
src/core/crdt/mvRegister.ts  <->  lean/CrdtBase/Crdt/MvRegister/Defs.lean
src/core/sqlEval.ts          <->  lean/CrdtBase/DiffTest/Main.lean (evaluator)
src/core/sql.ts              <->  lean/CrdtBase/Sql/Defs.lean (planner + ops)
src/core/compaction.ts       <->  lean/CrdtBase/Compaction/Defs.lean
src/core/replication.ts      <->  lean/CrdtBase/Replication/Defs.lean
```

### 13.2 Design Differences

| Aspect | TypeScript | Lean |
|--------|-----------|------|
| Collections | `Array`, `Map`, `Record` | `Finset`, `List`, `String -> Nat` |
| HLC storage | `bigint` via bit shift | `Nat` via multiplication |
| HLC clock API | `createHlcClock()` factory + standalone functions | `Hlc.now` / `Hlc.recv` returning `Option Hlc` |
| Deduplication | Explicit `dedupeBy*` functions | Implicit in `Finset` |
| Bounds checking | Runtime `throw` via `assertHlcInBounds` | Dependent types (`wallMs_lt`, `counter_lt`) |
| MV-Register pruning | `pruneDominatedBySameSite` in canonicalization | Not modeled (pure Finset union) |
| Binary encoding | MessagePack via `@msgpack/msgpack` | Not modeled (out of proof scope) |
| Merge dispatch | `switch` on `op.kind` string | Pattern match on `SqlWriteStatement` |
| Schema DDL | `information_schema` tables with LWW columns | Modeled through `SqlWriteStatement` variants |
| Tombstone GC | TTL-based `pruneRuntimeRowsForCompaction` | Not modeled (GC is runtime-only) |

### 13.3 Proof Inventory

| Tier | Count | Status |
|------|-------|--------|
| 1. CRDT Semilattice (LWW, PN, OR-Set, MV) | 21 theorems | All proved |
| 2. HLC Ordering | 21 theorems | All proved |
| 3. Convergence | 9 theorems | All proved |
| 4. Compaction | 10 theorems | All proved |
| 5. Tombstone | 3 theorems | All proved |
| 6. Table Composition | 16 theorems | All proved |
| 7. SQL Soundness | 10 theorems | All proved |
| 8. Replication | 4 theorems | All proved |
| **Total** | **94 theorems** | **All proved** |

The growth from ~59 to 94 theorems reflects:
- HLC Props expanded from 7 to 21 (bounds proofs, max3 lemmas, monotonicity aliases, `recv_wallMs_monotonic`)
- OR-Set Props added `or_set_merge_canonicalized` and `or_set_merge_idem_general` (idempotence chain)
- Table Props expanded from 8 to 16 (validity predicates, instantiated row theorems, lifted whole-table theorems)
- Compaction Props expanded from 7 to 10 (snapshot cutover, foldPrefixSuffix_eq_foldl_all)
- Convergence Props expanded from 5 to 9 (SameOps wrapper, LWW explicit, composite)
- Replication Props expanded from 2 to 4 (watermark alias, compacted prefix exclusion)

### 13.4 The Verification-Guided Development Loop

1. Write Lean definitions (`Defs.lean`) as the specification
2. Write TypeScript implementation
3. Run DRT: TypeScript test harness generates random inputs, pipes through both Lean executable and TypeScript, compares outputs
4. Write Lean proofs (`Props.lean`) to establish mathematical guarantees
5. Any DRT divergence is a bug in one codebase -- fix and re-verify

This follows the Cedar verification methodology: the Lean model is the source of truth for *what* the system should do, while the TypeScript is the source of truth for *how* it runs in production.
