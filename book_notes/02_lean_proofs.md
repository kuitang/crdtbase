# CrdtBase Lean 4 Formal Verification: Detailed Notes

## Overview

The `lean/` subdirectory of CrdtBase contains a formal specification and mechanized
proof suite written in Lean 4 (v4.27.0). It verifies the core algebraic properties
that every CRDT merge function must satisfy -- commutativity, associativity, and
idempotence -- plus convergence, compaction correctness, tombstone semantics, SQL
op-generation soundness, replication log safety, and HLC ordering invariants.

The project depends on **Batteries** (the Lean 4 community standard library) and
**Mathlib** (for `Finset`, `List.Perm`, and the `aesop` tactic). The global option
`autoImplicit = false` is set everywhere, following Cedar-style conventions: every
variable must be explicitly declared.

---

## File Dependency Architecture

```
CrdtBase.lean                      (root import -- pulls everything in)
  |
  +-- Hlc/Defs.lean                (HLC type, pack, compareWithSite, now, recv)
  +-- Hlc/Props.lean               (HLC ordering, monotonicity, total-order proofs)
  |
  +-- Crdt/Lww/Defs.lean           (LwwRegister structure and merge)
  +-- Crdt/Lww/Props.lean          (semilattice proofs: comm, assoc, idem)
  |     depends on Hlc/Props
  |
  +-- Crdt/PnCounter/Defs.lean     (PnCounter as String -> Nat functions)
  +-- Crdt/PnCounter/Props.lean    (semilattice proofs via Nat.max)
  |
  +-- Crdt/OrSet/Defs.lean         (OrSet with Finset elements and tombstones)
  +-- Crdt/OrSet/Props.lean        (semilattice proofs; uses Mathlib Finset + aesop)
  |
  +-- Crdt/MvRegister/Defs.lean    (MvRegister as Finset union)
  +-- Crdt/MvRegister/Props.lean   (semilattice proofs via Finset.union)
  |
  +-- Crdt/Table/Defs.lean         (Composite row state, whole-table merge)
  +-- Crdt/Table/Props.lean        (Lifting lemmas + operator commutativity)
  |
  +-- Convergence/Defs.lean        (applyOps, SameOps via List.Perm)
  +-- Convergence/Props.lean       (Abstract + concrete convergence theorems)
  |     depends on all Crdt/*/Props
  |
  +-- Compaction/Defs.lean         (foldPrefixSuffix, empty states)
  +-- Compaction/Props.lean        (compaction = full fold, idempotence)
  |
  +-- Tombstone/Defs.lean          (TombstoneState as LwwRegister Bool)
  +-- Tombstone/Props.lean         (delete-wins, write-resurrects, stability)
  |
  +-- Replication/Defs.lean        (LogEntry, readSince, getHead)
  +-- Replication/Props.lean       (readSince cursor safety)
  |
  +-- Sql/Defs.lean                (SQL AST, CRDT op generation, planner)
  +-- Sql/Props.lean               (type soundness, syncability, planner correctness)
  |
  +-- DiffTest/Main.lean           (JSONL bridge for differential random testing)
```

The dependency flow is strictly layered: `Hlc` is the foundation, `Crdt/*` types
build on it, `Convergence` composes all CRDT proofs, and `Compaction`/`Tombstone`
are derived consequences. The `Sql` and `Replication` modules are relatively
standalone.

---

## Data Structure Modeling

### HLC (Hybrid Logical Clock)

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Hlc/Defs.lean`

The HLC is modeled as a bounded structure with proof-carrying fields:

```lean
-- Hlc/Defs.lean:16-21
structure Hlc where
  wallMs : Nat
  counter : Nat
  wallMs_lt : wallMs < wallMsMax      -- wallMsMax = 2^48
  counter_lt : counter < counterMax   -- counterMax = 2^16
  deriving Repr, DecidableEq
```

The key design choice: bounds are carried as proof obligations in the structure
itself, not as separate invariants. This means every `Hlc` value is *by
construction* within range -- you cannot create an out-of-bounds HLC without
`sorry`. The `mk?` smart constructor enforces this at runtime with `if hWall : ...`
decidable checks.

**Packing** collapses the two fields into a single `Nat` for comparison:

```lean
-- Hlc/Defs.lean:26-27
def pack (h : Hlc) : Nat :=
  h.wallMs * counterMax + h.counter
```

**Extended comparison** (`compareWithSite`) implements lexicographic ordering over
`(pack, siteId)` using nested `if _ : ... then ... else ...` with named decidable
hypotheses. This is critical: the named hypotheses (`_` binds) are available in
the proof context when reasoning about branches.

```lean
-- Hlc/Defs.lean:34-44
def compareWithSite (a b : Hlc * String) : Ordering :=
  if _ : a.1.pack < b.1.pack then .lt
  else if _ : b.1.pack < a.1.pack then .gt
  else if _ : a.2 < b.2 then .lt
  else if _ : b.2 < a.2 then .gt
  else .eq
```

### LWW Register

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Lww/Defs.lean`

```lean
-- Lww/Defs.lean:8-12
structure LwwRegister (alpha : Type) where
  val  : alpha
  hlc  : Hlc
  site : String
  deriving Repr, DecidableEq
```

Merge is a simple conditional: if `a < b` by `compareWithSite`, take `b`;
otherwise take `a` (left-biased on ties):

```lean
-- Lww/Defs.lean:17-18
def merge {alpha : Type} (a b : LwwRegister alpha) : LwwRegister alpha :=
  if Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .lt then b else a
```

### PN-Counter

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/PnCounter/Defs.lean`

Modeled as two functions `String -> Nat` (not `HashMap`), which is ideal for
proofs since functions have extensional equality:

```lean
-- PnCounter/Defs.lean:6-8
structure PnCounter where
  inc : String -> Nat
  dec : String -> Nat
```

The custom `@[ext]` theorem enables the `ext` tactic to decompose equality into
pointwise equality at each site. Merge is pointwise `max`:

```lean
-- PnCounter/Defs.lean:28-31
@[simp]
def merge (a b : PnCounter) : PnCounter :=
  { inc := fun site => max (a.inc site) (b.inc site)
    dec := fun site => max (a.dec site) (b.dec site) }
```

### OR-Set

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/OrSet/Defs.lean`

Uses `Finset` (from Mathlib) for both elements and tombstones, which gives
decidable membership and set-algebraic lemmas for free:

```lean
-- OrSet/Defs.lean:20-22
structure OrSet (alpha : Type) (Hlc : Type) where
  elements   : Finset (OrSetElem alpha Hlc)
  tombstones : Finset (OrSetTag Hlc)
```

Merge unions both components, then canonicalizes (filters out tombstoned elements):

```lean
-- OrSet/Defs.lean:42-47
def OrSet.merge ... (a b : OrSet alpha Hlc) : OrSet alpha Hlc :=
  OrSet.canonicalize {
    elements := a.elements ∪ b.elements
    tombstones := a.tombstones ∪ b.tombstones
  }
```

### MV-Register

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/MvRegister/Defs.lean`

The simplest CRDT: merge is pure set union of observed values:

```lean
-- MvRegister/Defs.lean:29-31
def merge {alpha : Type} [DecidableEq alpha] (a b : MvRegister alpha) : MvRegister alpha :=
  { values := a.values ∪ b.values }
```

### Composite Table Row

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Table/Defs.lean`

A full row carries one column of each CRDT type plus a visibility flag:

```lean
-- Table/Defs.lean:11-16
structure TableRowState (alpha beta gamma Hlc : Type) where
  alive : LwwRegister Bool
  lwwCol : LwwRegister alpha
  counterCol : PnCounter
  setCol : OrSet beta Hlc
  registerCol : MvRegister gamma
```

Whole-table state is `kappa -> TableRowState ...` (a function from keys to rows),
and table merge is pointwise row merge.

---

## Complete Theorem Inventory

### Tier 1: CRDT Semilattice Properties (12 theorems)

| CRDT | Commutativity | Associativity | Idempotence |
|------|--------------|---------------|-------------|
| LWW Register | `lww_merge_comm_of_consistent` | `lww_merge_assoc_of_consistent` | `lww_merge_idem` |
| PN-Counter | `pn_counter_merge_comm` | `pn_counter_merge_assoc` | `pn_counter_merge_idem` |
| OR-Set | `or_set_merge_comm` | `or_set_merge_assoc` | `or_set_merge_idem` |
| MV-Register | `mv_register_merge_comm` | `mv_register_merge_assoc` | `mv_register_merge_idem` |

Plus OR-Set canonicalization properties:
- `or_set_canonicalize_idem`
- `or_set_canonicalize_no_tombstoned_tags`
- `or_set_canonicalize_preserves_visible_values`

Plus LWW event-consistency helpers:
- `lww_equal_key_implies_equal_payload`
- `dedup_rejects_conflicting_same_key`
- `lww_merge_comm_global_of_consistent`
- `lww_merge_assoc_global_of_consistent`

### Tier 2: HLC Ordering (14 theorems)

- `hlc_total_order` -- trichotomy of packed values
- `hlc_pack_preserves_order` -- higher wallMs implies higher pack
- `hlc_counter_breaks_tie` -- same wallMs: pack order = counter order
- `hlc_site_tiebreak_total` -- compareWithSite is total
- `compareWithSite_self_eq` -- reflexivity
- `compareWithSite_swap_lt` / `compareWithSite_swap_gt` -- antisymmetry
- `compareWithSite_trans_lt` / `compareWithSite_trans_gt` -- transitivity
- `pack_lt_of_same_wall_counter_lt` -- helper for monotonicity
- `hlc_now_monotonic` / `hlc_now_strict_monotonic` -- now() strictly increases
- `hlc_recv_monotonic` / `hlc_recv_strict_monotonic` -- recv() strictly increases
- `recv_none_of_drift` -- drift rejection
- `recv_some_bounds` / `now_some_bounds` -- output stays in bounds
- `recv_wallMs_monotonic` -- wall component is monotonically non-decreasing
- `max3_ge_left` / `max3_ge_mid` / `max3_ge_right` -- max3 dominance

### Tier 3: Convergence (7 theorems)

- `convergence_of_perm` -- abstract: right-commutative folds are perm-invariant
- `convergence_of_same_ops` -- same, via SameOps wrapper
- `convergence_of_comm_assoc` -- constructs RightCommutative from comm+assoc
- `convergence_lww` / `convergence_lww_of_consistent` -- LWW instantiation
- `convergence_pn_counter` -- PN-Counter instantiation
- `convergence_or_set` -- OR-Set instantiation
- `convergence_mv_register` -- MV-Register instantiation
- `convergence_composite` -- 2-column composite row

### Tier 4: Compaction (7 theorems)

- `foldPrefixSuffix_eq_foldl` -- split compaction = full fold
- `foldPrefixSuffix_eq_foldl_all` -- universally quantified over split point
- `compaction_preserves_state` -- canonical form: prefix fold then suffix fold
- `compaction_idempotent` -- re-compacting with no new ops is identity
- `pn_counter_compaction_preserves_state`
- `or_set_compaction_preserves_state`
- `mv_register_compaction_preserves_state`
- `lww_compaction_preserves_state`

### Tier 5: Tombstone (3 theorems)

- `delete_wins_if_later` -- later delete beats earlier write
- `write_resurrects_if_later` -- later write beats earlier delete
- `tombstone_stable_without_new_writes` -- idempotent re-merge

### Table Composition (9 theorems)

- `table_merge_comm_of_row_comm` / `table_merge_assoc_of_row_assoc` / `table_merge_idem_of_row_idem`
- `apply_counter_preserves_visibility` / `apply_set_preserves_visibility` / `apply_register_preserves_visibility`
- `row_exists_counter_commute` / `row_exists_set_commute` / `row_counter_register_commute`
- `modify_row_at_disjoint_commute`

### SQL Soundness (8 theorems)

- `write_ops_type_sound` -- all emitted ops have valid CRDT type tags
- `write_ops_syncable` -- all emitted ops have non-empty sync identifiers
- `no_nonsync_for_valid_crdt_writes` -- explicit field-level restatement
- `planner_partition_default_route`
- `planner_partition_sound` -- equality predicate routes to correct partition
- `planner_partition_sound_all_partitions` / `planner_partition_sound_all_partitions_of_no_match`
- `planner_filter_preservation` / `planner_filter_preservation_no_partition` / `planner_filter_preservation_all_partitions`

### Replication (2 theorems)

- `mem_takeContiguousFrom_mem` -- contiguous subsequence membership
- `readSince_mem_gt_since` -- all returned seqs are strictly greater than cursor

---

## Proof Techniques Used

### Tactic Palette

| Tactic | Usage Pattern |
|--------|--------------|
| `simp` | Workhorse for definitional unfolding and rewriting. Used with explicit lemma sets (`simp [Hlc.recv, ...]`) to control unfolding depth. |
| `ext` | Extensionality for `PnCounter` (custom `@[ext]`), `Finset`, and `fun`-typed table states (`funext key`). |
| `cases` | Destructuring `Ordering` variants (`cases hab : ... with \| lt => ... \| eq => ... \| gt => ...`). Also used on structures (`cases a with \| mk ... => ...`). |
| `omega` | Not directly used (surprisingly), but `Nat.lt_irrefl`, `Nat.lt_asymm`, `Nat.lt_trans` etc. serve the same purpose for natural number reasoning. |
| `aesop` | Used in OR-Set associativity proof to close complex Finset membership goals after `simp` reduces them. |
| `subst` | Key in LWW proofs: when event-consistency gives `a = b`, `subst` eliminates the variable. |
| `by_cases` | Pervasive in HLC proofs for case-splitting on `<` comparisons. |
| `calc` | Used for multi-step equalities/inequalities, especially in `hlc_recv_monotonic`. |
| `funext` | For table-level proofs where equality of functions requires pointwise reasoning. |
| `simpa` | Combines `simp` with `assumption`, used extensively for clean proof closures. |
| `rfl` | Closes goals where both sides are definitionally equal after `cases`. Used elegantly in table operator commutativity proofs. |
| `congrArg` | Extracts field equalities from structure equalities (e.g., `congrArg Hlc.wallMs hEq`). |

---

## Deep Dive: Three Elegant Proofs

### 1. PN-Counter Semilattice (The One-Liner Trio)

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/PnCounter/Props.lean`

These three proofs are the most elegant in the entire codebase, each requiring
exactly one line:

```lean
-- PnCounter/Props.lean:8-21
theorem pn_counter_merge_comm (a b : PnCounter) :
    PnCounter.merge a b = PnCounter.merge b a := by
  ext site <;> simp [PnCounter.merge, Nat.max_comm]

theorem pn_counter_merge_assoc (a b c : PnCounter) :
    PnCounter.merge (PnCounter.merge a b) c =
      PnCounter.merge a (PnCounter.merge b c) := by
  ext site <;> simp [PnCounter.merge, Nat.max_assoc]

theorem pn_counter_merge_idem (a : PnCounter) :
    PnCounter.merge a a = a := by
  ext site <;> simp [PnCounter.merge]
```

**Step-by-step for commutativity:**

1. **`ext site`** -- The custom `@[ext]` theorem on `PnCounter` (defined in Defs.lean)
   splits the goal `PnCounter.merge a b = PnCounter.merge b a` into two subgoals:
   - `forall site, max (a.inc site) (b.inc site) = max (b.inc site) (a.inc site)`
   - `forall site, max (a.dec site) (b.dec site) = max (b.dec site) (a.dec site)`

2. **`<;>`** -- The semicolon combinator applies the following tactic to *all*
   remaining subgoals simultaneously.

3. **`simp [PnCounter.merge, Nat.max_comm]`** -- Unfolds the merge definition,
   then applies `Nat.max_comm` (from Batteries) to close both goals.

**Why this is elegant:** The modeling choice of `String -> Nat` (instead of
`HashMap`) is what makes these proofs trivial. With `HashMap`, you would need to
reason about finite map equality, key enumeration, and missing-key defaults.
With pure functions, `ext` gives you pointwise reasoning for free, and the
proof reduces to the corresponding property of `Nat.max`. The entire semilattice
proof for PN-Counter is 6 lines of actual proof text.

### 2. Convergence via RightCommutative Construction

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Convergence/Props.lean`

This is the crown jewel -- the abstract convergence theorem that says "if merge
forms a semilattice, then fold over any permutation of the same operations
converges to the same state."

```lean
-- Convergence/Props.lean:27-42
theorem convergence_of_comm_assoc {alpha : Type}
    (merge : alpha -> alpha -> alpha)
    (hComm : forall a b : alpha, merge a b = merge b a)
    (hAssoc : forall a b c : alpha, merge (merge a b) c = merge a (merge b c))
    (init : alpha) {ops1 ops2 : List alpha}
    (hPerm : List.Perm ops1 ops2) :
    applyOps merge init ops1 = applyOps merge init ops2 := by
  letI : RightCommutative merge := <<by
    intro a b c
    calc
      merge (merge a b) c = merge a (merge b c) := hAssoc a b c
      _ = merge a (merge c b) := by rw [hComm b c]
      _ = merge (merge a c) b := (hAssoc a c b).symm
    >>
  exact convergence_of_perm merge init hPerm
```

**Step-by-step:**

1. **The bridge insight:** Mathlib already has `List.Perm.foldl_eq` which says that
   `foldl` over a permutation gives the same result *if* the step function is
   `RightCommutative` (i.e., `f (f a b) c = f (f a c) b`). The proof's job is to
   construct a `RightCommutative` instance from the more natural
   commutativity + associativity axioms.

2. **`letI : RightCommutative merge`** -- Introduces a local typeclass instance.
   The proof obligation is: `forall a b c, merge (merge a b) c = merge (merge a c) b`.

3. **The `calc` chain** -- This is the algebraic heart:
   ```
   merge (merge a b) c
     = merge a (merge b c)       -- by associativity
     = merge a (merge c b)       -- by commutativity on the inner pair
     = merge (merge a c) b       -- by associativity (reversed)
   ```
   Each step uses exactly one axiom. The `.symm` at the end flips the direction
   of the associativity rewrite.

4. **`exact convergence_of_perm merge init hPerm`** -- With the `RightCommutative`
   instance in scope, this delegates to the simpler theorem that just calls
   `hPerm.foldl_eq`.

**Why this is elegant:** It cleanly separates the algebraic bridge (comm + assoc
implies right-commutative) from the permutation lemma (right-commutative foldl is
perm-invariant). The `calc` proof reads like a textbook algebraic derivation.
The concrete per-CRDT convergence theorems then become one-liners:

```lean
-- Convergence/Props.lean:127-131
theorem convergence_pn_counter
    (init : PnCounter) {ops1 ops2 : List PnCounter}
    (hPerm : List.Perm ops1 ops2) :
    applyOps PnCounter.merge init ops1 = applyOps PnCounter.merge init ops2 := by
  simpa using convergence_of_perm PnCounter.merge init hPerm
```

For PN-Counter, OR-Set, and MV-Register, the proof doesn't even need to go through
`convergence_of_comm_assoc` -- it uses `convergence_of_perm` directly because
`Std.Commutative` and `Std.Associative` instances are registered, and Mathlib can
derive `RightCommutative` from those.

### 3. LWW Associativity Under Event-Consistency

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Lww/Props.lean`

This is the most technically demanding proof in the codebase because LWW merge
is not unconditionally associative -- it requires the event-consistency invariant.

```lean
-- Lww/Props.lean:51-82
theorem lww_merge_assoc_of_consistent {alpha : Type} (a b c : LwwRegister alpha)
    (hAB : LwwConsistentPair a b)
    (hBC : LwwConsistentPair b c)
    : LwwRegister.merge (LwwRegister.merge a b) c =
      LwwRegister.merge a (LwwRegister.merge b c) := by
  unfold LwwRegister.merge
  cases hab : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) <;>
    cases hbc : Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) <;>
    cases hac : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) <;>
    simp [hab, hbc, hac]
  -- 6 impossible cases remain after simp closes the consistent ones
  . have hacLt := compareWithSite_trans_lt hab hbc; simp [hac] at hacLt
  . have hacLt := compareWithSite_trans_lt hab hbc; simp [hac] at hacLt
  . have habEq : a = b := hAB hab; have hbcEq : b = c := hBC hbc
    subst habEq; subst hbcEq
    have hacEq := compareWithSite_self_eq (a.hlc, a.site); simp [hac] at hacEq
  . have habEq : a = b := hAB hab; subst habEq; simp [hac] at hbc
  . have hbcEq : b = c := hBC hbc; subst hbcEq; simp [hac] at hab
  . have hacGt := compareWithSite_trans_gt hab hbc; simp [hac] at hacGt
```

**Step-by-step:**

1. **`unfold LwwRegister.merge`** -- Exposes the `if ... then b else a` conditionals
   on both sides of the equation.

2. **Triple case split** -- `cases hab ... <;> cases hbc ... <;> cases hac ...`
   generates 3 x 3 x 3 = 27 subgoals, one for each combination of `{lt, eq, gt}`
   for the three pairwise comparisons `(a,b)`, `(b,c)`, `(a,c)`.

3. **`simp [hab, hbc, hac]`** -- After the case split, each subgoal has specific
   `Ordering` values for all three comparisons. The `simp` step evaluates the
   `if` branches and closes the 21 consistent cases (where the three comparisons
   form a valid ordering relationship, e.g., `a < b` and `b < c` and `a < c`).

4. **The 6 remaining cases** are the *impossible* ones -- combinations that
   violate transitivity or consistency:
   - `a < b, b < c, a = c` -- contradicts transitivity (proven via `compareWithSite_trans_lt`)
   - `a < b, b < c, a > c` -- same contradiction
   - `a = b, b = c, a != c` -- event-consistency says `a = b` and `b = c`, so `a = c`
     must hold. `subst` eliminates both, then `compareWithSite_self_eq` closes it.
   - `a = b, b > c, a < c` -- `subst` makes `a = b`, so `b > c` and `a < c` conflict
   - `a > b, b = c, a < c` -- similar after `subst`
   - `a > b, b > c, a < c` -- contradicts transitivity via `compareWithSite_trans_gt`

5. Each impossible case is discharged by deriving a contradiction: either
   transitivity gives a comparison result that conflicts with the case hypothesis,
   or event-consistency plus `subst` collapses two variables into one and the
   remaining comparison is self-contradictory.

**Why this is elegant:** The 27-way case split sounds brute-force, but it is
actually the cleanest approach for a comparison-based merge. Lean's `<;>` combinator
means you write the `cases` and `simp` once and it applies to all branches
simultaneously. Only 6 cases survive, and each is closed with a one-liner
contradiction argument. The proof structure mirrors the mathematical argument
exactly: "for any total order, max is associative; the only subtle cases are
ties, where event-consistency substitutes equality."

---

## Key Design Decisions

### Functions vs. HashMap for PN-Counter

The PN-Counter is modeled as `String -> Nat` in the proof layer (Defs.lean) but
as `HashMap String Nat` in the executable DiffTest bridge (Main.lean). This is the
Cedar-style separation: the *specification* uses the mathematically convenient type,
and the *implementation* uses the performant type. Differential testing ensures they
agree.

### Event-Consistency as a Theorem Precondition

LWW commutativity and associativity are conditional on `LwwConsistentPair`:

```lean
-- Lww/Props.lean:11-12
def LwwConsistentPair {alpha : Type} (a b : LwwRegister alpha) : Prop :=
  Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = Ordering.eq -> a = b
```

This says: if two LWW registers have the same `(hlc, site)` key, they must be
identical (same payload). This is an operational invariant -- if violated (e.g.,
cloned site IDs), the system provides no convergence guarantee. The proofs make
this assumption explicit rather than silently assuming it.

### Finset for OR-Set (Mathlib Dependency)

The OR-Set and MV-Register use `Finset` from Mathlib, which provides:
- Decidable membership (`x in s` is decidable)
- Set algebra (`union`, `filter`, `image`) with associated lemmas
- The `aesop` tactic for automated membership reasoning

This is the main reason for the Mathlib dependency. The tradeoff is compilation
time vs. proof automation quality.

### Private Helper Theorems in HLC

The HLC Props file defines a private `siteLexLt` predicate and three private helper
theorems (`compareWithSite_eq_lt_iff`, `siteLexLt_trans`, `compareWithSite_gt_of_siteLexLt`)
that bridge between the syntactic `compareWithSite` definition (with its nested
`if`s) and a semantic lexicographic ordering. This abstraction barrier keeps the
public-facing theorems clean while containing the if-branch reasoning in one place.

### Compaction as foldl Splitting

Compaction correctness reduces to a single library lemma:

```lean
-- Compaction/Props.lean:39-45
theorem compaction_preserves_state {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (preOps postOps : List alpha) :
    List.foldl step (List.foldl step init preOps) postOps =
      List.foldl step init (preOps ++ postOps) := by
  exact (List.foldl_append ...).symm
```

This is `List.foldl_append` from the standard library, applied in reverse. The
entire compaction proof machinery is an elegant wrapper around this single fact:
splitting a fold at any point and resuming is the same as folding the whole list.
No commutativity or associativity of the merge function is needed -- this is a
property of `foldl` itself.

---

## Proof Architecture Summary

The proof architecture follows a clear layering strategy:

1. **Foundation layer** (HLC): Establish that `compareWithSite` is a strict total
   order with antisymmetry, transitivity, and reflexivity. All proofs here are
   direct natural number reasoning.

2. **CRDT layer**: Each CRDT type proves its own semilattice triple (comm, assoc,
   idem). The techniques vary by type:
   - **LWW**: Case analysis on comparison results + HLC order properties
   - **PN-Counter**: Extensionality + `Nat.max` properties
   - **OR-Set**: Finset algebra + `aesop`
   - **MV-Register**: Finset union algebra

3. **Lifting layer** (Table): Proves that pointwise application of row merges
   preserves semilattice properties, and that independent column operations commute.
   These proofs are almost all `cases row; rfl`.

4. **Composition layer** (Convergence): Takes the per-CRDT semilattice proofs and
   composes them with the permutation-invariance of foldl to prove system-wide
   convergence. The key bridge is constructing `RightCommutative` from `comm + assoc`.

5. **Application layer** (Compaction, Tombstone, SQL, Replication): Derives
   domain-specific consequences. Compaction uses `List.foldl_append`. Tombstones
   reuse LWW proofs directly. SQL proofs use `decide` and boolean reflection.

The total proof codebase is approximately 900 lines of proof text spread across
12 `Props.lean` files, covering 60+ theorems. Every theorem has a docstring, and
the proofs are readable enough to serve as documentation of the system's
correctness invariants.
