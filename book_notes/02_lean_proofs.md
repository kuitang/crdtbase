# CrdtBase Lean 4 Formal Verification: Detailed Notes

## Overview

The `lean/` subdirectory of CrdtBase contains a formal specification and mechanized
proof suite written in Lean 4 (v4.27.0). It verifies the core algebraic properties
that every CRDT merge function must satisfy -- commutativity, associativity, and
idempotence -- plus convergence, table composition, compaction correctness, tombstone
semantics, SQL op-generation soundness, replication log safety, and HLC ordering
invariants.

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
  +-- Crdt/OrSet/Props.lean        (semilattice proofs + canonicalization chain + aesop)
  |
  +-- Crdt/MvRegister/Defs.lean    (MvRegister as Finset union)
  +-- Crdt/MvRegister/Props.lean   (semilattice proofs via Finset.union)
  |
  +-- Crdt/Table/Defs.lean         (Composite row state, whole-table merge, apply ops)
  +-- Crdt/Table/Props.lean        (Validity predicates, lifting, operator commutativity)
  |     depends on all Crdt/*/Props
  |
  +-- Convergence/Defs.lean        (applyOps, SameOps via List.Perm)
  +-- Convergence/Props.lean       (Abstract + concrete convergence theorems)
  |     depends on all Crdt/*/Props
  |
  +-- Compaction/Defs.lean         (foldPrefixSuffix, empty states)
  +-- Compaction/Props.lean        (compaction = full fold, snapshot cutover, idempotence)
  |
  +-- Tombstone/Defs.lean          (TombstoneState as LwwRegister Bool)
  +-- Tombstone/Props.lean         (delete-wins, write-resurrects, stability)
  |
  +-- Replication/Defs.lean        (LogEntry, readSince, getHead, canonicalSeqs)
  +-- Replication/Props.lean       (readSince cursor safety + compaction exclusion)
  |
  +-- Sql/Defs.lean                (SQL AST, CRDT op generation, planner)
  +-- Sql/Props.lean               (type soundness, syncability, planner correctness)
  |
  +-- DiffTest/Main.lean           (JSONL bridge for differential random testing)
```

The dependency flow is strictly layered: `Hlc` is the foundation, `Crdt/*` types
build on it, `Table` composes all per-CRDT proofs into composite row/table
theorems, `Convergence` composes the CRDT semilattice proofs with permutation
invariance, and `Compaction`/`Tombstone`/`Replication` are derived consequences.
The `Sql` module is relatively standalone.

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

The proof suite now contains **76 theorems** across 8 tiers (plus supporting
private lemmas), spread over 12 `Props.lean` files.

### Tier 1: CRDT Semilattice Properties (16 theorems)

| CRDT | Commutativity | Associativity | Idempotence |
|------|--------------|---------------|-------------|
| LWW Register | `lww_merge_comm_of_consistent` | `lww_merge_assoc_of_consistent` | `lww_merge_idem` |
| PN-Counter | `pn_counter_merge_comm` | `pn_counter_merge_assoc` | `pn_counter_merge_idem` |
| OR-Set | `or_set_merge_comm` | `or_set_merge_assoc` | `or_set_merge_idem` |
| MV-Register | `mv_register_merge_comm` | `mv_register_merge_assoc` | `mv_register_merge_idem` |

Plus OR-Set canonicalization chain (4 theorems):
- `or_set_canonicalize_idem` -- canonicalization is idempotent
- `or_set_canonicalize_no_tombstoned_tags` -- output has no tombstoned elements
- `or_set_canonicalize_preserves_visible_values` -- visible-value semantics unchanged
- `or_set_merge_canonicalized` -- merge output is always canonicalized

Plus LWW event-consistency helpers (4 theorems):
- `lww_equal_key_implies_equal_payload`
- `dedup_rejects_conflicting_same_key`
- `lww_merge_comm_global_of_consistent`
- `lww_merge_assoc_global_of_consistent`

Plus OR-Set precondition-free idempotence (1 theorem):
- `or_set_merge_idem_general` -- `merge (merge a b) (merge a b) = merge a b`

### Tier 2: HLC Ordering (19 theorems)

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

### Tier 3: Convergence (9 theorems)

- `convergence_of_perm` -- abstract: right-commutative folds are perm-invariant
- `convergence_of_same_ops` -- same, via SameOps wrapper
- `convergence_of_comm_assoc` -- constructs RightCommutative from comm+assoc
- `convergence_lww` / `convergence_lww_of_consistent` -- LWW instantiation
- `convergence_pn_counter` -- PN-Counter instantiation
- `convergence_or_set` -- OR-Set instantiation
- `convergence_mv_register` -- MV-Register instantiation
- `convergence_composite` -- 2-column composite row

### Tier 4: Table Composition (16 theorems)

Row-level semilattice under validity predicates (3 theorems):
- `mergeTableRow_comm_of_valid` -- row commutativity under `ValidTableRowPair`
- `mergeTableRow_assoc_of_valid` -- row associativity under `ValidTableRowTriple`
- `mergeTableRow_idem_of_valid` -- row idempotence under OR-Set canonicalization

Lifted whole-table theorems (3 theorems):
- `mergeTable_comm_of_valid` -- table commutativity under `ValidTableState`
- `mergeTable_assoc_of_valid` -- table associativity under `ValidTableStateTriple`
- `mergeTable_idem_of_valid` -- table idempotence under `ValidTableStateIdem`

Operator visibility preservation (3 theorems):
- `apply_counter_preserves_visibility` -- counter updates do not change row visibility
- `apply_set_preserves_visibility` -- OR-Set updates do not change row visibility
- `apply_register_preserves_visibility` -- MV-register updates do not change row visibility

Column commutativity (3 theorems):
- `row_exists_counter_commute` -- row-existence and counter updates commute
- `row_exists_set_commute` -- row-existence and OR-Set updates commute
- `row_counter_register_commute` -- counter and MV-register updates commute

Disjoint key commutativity (1 theorem):
- `modify_row_at_disjoint_commute` -- updates at distinct keys commute at table level

Plus 3 validity predicate definitions used as theorem preconditions:
- `ValidTableState`, `ValidTableStateTriple`, `ValidTableStateIdem`

### Tier 5: Compaction (9 theorems)

- `foldPrefixSuffix_eq_foldl` -- split compaction = full fold
- `foldPrefixSuffix_eq_foldl_all` -- universally quantified over split point
- `compaction_preserves_state` -- canonical form: prefix fold then suffix fold
- `compaction_idempotent` -- re-compacting with no new ops is identity
- `pn_counter_compaction_preserves_state` -- PN-Counter specialization
- `or_set_compaction_preserves_state` -- OR-Set specialization
- `mv_register_compaction_preserves_state` -- MV-Register specialization
- `lww_compaction_preserves_state` -- LWW specialization (with `Option` base)
- `snapshot_then_suffix_replay_eq_full_fold` -- snapshot cutover law
- `snapshot_cutover_idempotent_without_new_suffix` -- no-op with empty suffix

### Tier 6: Tombstone (3 theorems)

- `delete_wins_if_later` -- later delete beats earlier write
- `write_resurrects_if_later` -- later write beats earlier delete
- `tombstone_stable_without_new_writes` -- idempotent re-merge

### Tier 7: SQL Soundness (8 theorems)

- `write_ops_type_sound` -- all emitted ops have valid CRDT type tags
- `write_ops_syncable` -- all emitted ops have non-empty sync identifiers
- `no_nonsync_for_valid_crdt_writes` -- explicit field-level restatement
- `planner_partition_default_route`
- `planner_partition_sound` -- equality predicate routes to correct partition
- `planner_partition_sound_all_partitions` / `planner_partition_sound_all_partitions_of_no_match`
- `planner_filter_preservation` / `planner_filter_preservation_no_partition` / `planner_filter_preservation_all_partitions`

### Tier 8: Replication (3 theorems)

- `mem_takeContiguousFrom_mem` -- contiguous subsequence membership
- `readSince_mem_gt_since` -- all returned seqs are strictly greater than cursor
- `readSince_after_watermark_only_returns_gt_watermark` -- watermark form of cursor safety
- `readSince_compacted_prefix_exclusion` -- compacted entries are never replayed

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
| `by_cases` | Pervasive in HLC proofs for case-splitting on `<` comparisons. Also in `modify_row_at_disjoint_commute` for key equality. |
| `calc` | Used for multi-step equalities/inequalities, especially in `hlc_recv_monotonic` and `modify_row_at_disjoint_commute`. |
| `funext` | For table-level proofs where equality of functions requires pointwise reasoning. Central to the lifting pattern. |
| `simpa` | Combines `simp` with `assumption`, used extensively for clean proof closures. |
| `rfl` | Closes goals where both sides are definitionally equal after `cases`. Used elegantly in all table operator commutativity proofs. |
| `congrArg` | Extracts field equalities from structure equalities (e.g., `congrArg Hlc.wallMs hEq`). |

---

## Deep Dive: Five Elegant Proofs

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
-- Convergence/Props.lean:28-42
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
-- Convergence/Props.lean:126-131
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

### 4. Table Composition: Validity Predicates and the Lifting Pattern

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/Table/Props.lean`

The table composition proofs represent the most architecturally significant
addition to the proof suite. They show that composite rows -- carrying one column
of each CRDT type -- preserve semilattice properties when each column's merge
function does so under the appropriate preconditions.

The key innovation is the **validity predicate** design. Rather than requiring
unconditional semilattice properties (which LWW does not have), the proofs
thread preconditions through structured predicates:

```lean
-- Table/Props.lean:58-63
structure ValidTableRowPair (a b : TableRowState alpha beta gamma Hlc) : Prop where
  alive_consistent   : LwwConsistentPair a.alive b.alive
  lwwCol_consistent  : LwwConsistentPair a.lwwCol b.lwwCol
  setCol_a_clean     : forall x in a.setCol.elements, x.tag not_in a.setCol.tombstones
  setCol_b_clean     : forall x in b.setCol.elements, x.tag not_in b.setCol.tombstones
```

For three-way associativity, a separate `ValidTableRowTriple` captures pairwise
LWW consistency for `(a,b)` and `(b,c)`:

```lean
-- Table/Props.lean:79-83
structure ValidTableRowTriple (a b c : TableRowState alpha beta gamma Hlc) : Prop where
  alive_ab : LwwConsistentPair a.alive b.alive
  alive_bc : LwwConsistentPair b.alive c.alive
  lww_ab   : LwwConsistentPair a.lwwCol b.lwwCol
  lww_bc   : LwwConsistentPair b.lwwCol c.lwwCol
```

Row-level commutativity then assembles per-column proofs via a 5-tuple:

```lean
-- Table/Props.lean:66-75
theorem mergeTableRow_comm_of_valid
    (a b : TableRowState alpha beta gamma Hlc)
    (hValid : ValidTableRowPair a b)
    : mergeTableRow a b = mergeTableRow b a := by
  simp only [mergeTableRow, TableRowState.mk.injEq]
  exact <<lww_merge_comm_of_consistent a.alive b.alive hValid.alive_consistent,
         lww_merge_comm_of_consistent a.lwwCol b.lwwCol hValid.lwwCol_consistent,
         pn_counter_merge_comm a.counterCol b.counterCol,
         or_set_merge_comm a.setCol b.setCol,
         mv_register_merge_comm a.registerCol b.registerCol>>
```

The lifting from row-level to whole-table is accomplished via `funext`:

```lean
-- Table/Props.lean:125-130
theorem mergeTable_comm_of_valid {kappa : Type}
    (a b : TableState kappa alpha beta gamma Hlc)
    (hValid : ValidTableState a b)
    : mergeTable a b = mergeTable b a := by
  funext key
  exact mergeTableRow_comm_of_valid (a key) (b key) (hValid key)
```

**Why this is significant:** The table composition proofs close the gap between
individual CRDT correctness and system-level correctness. The validity predicates
encode the operational invariants that the runtime must maintain (event-consistency
for LWW columns, canonicalization for OR-Set columns), and the theorems state
precisely what guarantees follow from those invariants. This is the Cedar-style
approach at its best: the spec makes system-level assumptions explicit.

### 5. OR-Set Idempotence Chain

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Crdt/OrSet/Props.lean`

OR-Set idempotence is the trickiest of the semilattice properties because merge
includes a canonicalization step that filters out tombstoned elements. Naively,
`merge a a` might not equal `a` if `a` has elements whose tags appear in its
own tombstone set (i.e., `a` is not canonicalized).

The proof suite resolves this with a four-theorem chain:

**Step 1:** Canonicalization is idempotent.

```lean
-- OrSet/Props.lean:9-12
theorem or_set_canonicalize_idem {alpha Hlc : Type} [DecidableEq alpha] [DecidableEq Hlc]
    (a : OrSet alpha Hlc) :
    OrSet.canonicalize (OrSet.canonicalize a) = OrSet.canonicalize a := by
  ext x <;> simp [OrSet.canonicalize]
```

**Step 2:** Canonicalized output has no tombstoned element tags.

```lean
-- OrSet/Props.lean:15-19
theorem or_set_canonicalize_no_tombstoned_tags {alpha Hlc : Type} ...
    (a : OrSet alpha Hlc) :
    forall x, x in (OrSet.canonicalize a).elements -> x.tag not_in (OrSet.canonicalize a).tombstones := by
  intro x hx
  exact (Finset.mem_filter.mp hx).2
```

**Step 3:** Merge output is always canonicalized.

```lean
-- OrSet/Props.lean:62-67
theorem or_set_merge_canonicalized {alpha Hlc : Type} ...
    (a b : OrSet alpha Hlc) :
    forall x in (OrSet.merge a b).elements, x.tag not_in (OrSet.merge a b).tombstones := by
  intro x hx
  simp [OrSet.merge] at hx |-
  exact hx.2
```

**Step 4:** Precondition-free idempotence for merge outputs.

```lean
-- OrSet/Props.lean:71-74
theorem or_set_merge_idem_general {alpha Hlc : Type} ...
    (a b : OrSet alpha Hlc) :
    OrSet.merge (OrSet.merge a b) (OrSet.merge a b) = OrSet.merge a b := by
  exact or_set_merge_idem (OrSet.merge a b) (or_set_merge_canonicalized a b)
```

The chain works as follows: `or_set_merge_idem` requires a cleanness precondition
(no element tag in tombstones). `or_set_merge_canonicalized` proves that any
merge output satisfies this precondition. `or_set_merge_idem_general` composes
the two: since `merge a b` is always clean, `merge (merge a b) (merge a b) =
merge a b`. This is exactly the property needed by the table composition layer
(Tier 4), where `mergeTableRow_idem_of_valid` requires OR-Set canonicalization.

**Why this is elegant:** The `or_set_merge_idem_general` proof is a single `exact`
-- one line. All the work was already done by the preceding lemmas. This
composition pattern, where each lemma does exactly one thing and the final
theorem is a trivial assembly, is characteristic of well-structured Lean proofs.

---

## Deep Dive: Replication and Compaction Proofs

### Replication Log Safety

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Replication/Props.lean` (62 lines)

The replication module proves three theorems about the `readSince` function, which
returns log entries strictly newer than a watermark cursor.

The central theorem is `readSince_mem_gt_since`:

```lean
-- Replication/Props.lean:26-42
theorem readSince_mem_gt_since
    (entries : List LogEntry) (siteId : String) (since seq : Nat)
    (hMem : seq in readSince entries siteId since) :
    seq > since := by
  unfold readSince at hMem
  have hInFilter : seq in (canonicalSeqs entries siteId).filter (fun candidate => candidate > since) :=
    mem_takeContiguousFrom_mem
      (expected := since + 1) (seq := seq)
      (seqs := (canonicalSeqs entries siteId).filter (fun candidate => candidate > since))
      hMem
  have hTrue : decide (seq > since) = true := (List.mem_filter.mp hInFilter).2
  by_cases hGt : seq > since
  . exact hGt
  . have hFalse : decide (seq > since) = false := by simp [hGt]
    rw [hFalse] at hTrue
    contradiction
```

The proof first unfolds `readSince`, which composes `canonicalSeqs` (site-filtered
sorted sequence numbers) with `filter` (keep only those > watermark) with
`takeContiguousFrom` (take the maximal contiguous prefix starting at
`since + 1`). The helper `mem_takeContiguousFrom_mem` establishes that membership
in `takeContiguousFrom`'s output implies membership in the input list, which is
the filtered list. Then `List.mem_filter` extracts the filter predicate, and
`by_cases` on the decidable `>` closes the proof.

The compaction exclusion theorem builds directly on cursor safety:

```lean
-- Replication/Props.lean:52-58
theorem readSince_compacted_prefix_exclusion
    (entries : List LogEntry) (siteId : String) (watermark seq : Nat)
    (hLe : seq <= watermark) :
    seq not_in readSince entries siteId watermark := by
  intro hMem
  have hGt := readSince_after_watermark_only_returns_gt_watermark entries siteId watermark seq hMem
  exact (Nat.not_lt_of_ge hLe) hGt
```

This is the formal guarantee that compacted log entries (those at or below the
watermark) are never replayed to clients. The proof is a one-step contradiction:
if `seq <= watermark` and `seq > watermark`, we have `not_lt_of_ge` against `hGt`.

### Compaction Correctness

**File:** `/home/kuitang/git/crdtbase/lean/CrdtBase/Compaction/Props.lean` (120 lines)

Compaction correctness reduces to a single standard library lemma, but the file
develops a complete theory around it.

The foundational theorem is `foldPrefixSuffix_eq_foldl`:

```lean
-- Compaction/Props.lean:10-25
theorem foldPrefixSuffix_eq_foldl {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (ops : List alpha) (split : Nat) :
    foldPrefixSuffix step init ops split = List.foldl step init ops := by
  calc
    foldPrefixSuffix step init ops split
        = List.foldl step (List.foldl step init (List.take split ops)) (List.drop split ops) := by
            rfl
    _ = List.foldl step init (List.take split ops ++ List.drop split ops) := by
          simpa using
            (List.foldl_append ...).symm
    _ = List.foldl step init ops := by
          exact congrArg (List.foldl step init) (List.take_append_drop split ops)
```

The `calc` chain is pedagogically clear: (1) unfold `foldPrefixSuffix` to its
definition as nested `foldl`; (2) apply `List.foldl_append` in reverse to merge
the two folds; (3) apply `List.take_append_drop` to recover the original list.

The per-CRDT specializations instantiate this generic theorem:

```lean
-- Compaction/Props.lean:55-64
theorem pn_counter_compaction_preserves_state
    (ops : List PnCounter) (split : Nat) :
    foldPrefixSuffix PnCounter.merge pnCounterEmpty ops split =
      List.foldl PnCounter.merge pnCounterEmpty ops := by
  simpa using
    (foldPrefixSuffix_eq_foldl
      (step := PnCounter.merge) (init := pnCounterEmpty) (ops := ops) (split := split))
```

Note how the LWW specialization differs: it uses `Option (LwwRegister alpha)` as
the initial state (since there may be no initial value), with `lwwStep` as the
step function:

```lean
-- Compaction/Props.lean:93-102
theorem lww_compaction_preserves_state {alpha : Type}
    (ops : List (LwwRegister alpha)) (split : Nat) :
    foldPrefixSuffix lwwStep none ops split =
      List.foldl lwwStep none ops := by
  simpa using
    (foldPrefixSuffix_eq_foldl
      (step := lwwStep) (init := (none : Option (LwwRegister alpha)))
      (ops := ops) (split := split))
```

The snapshot cutover theorems formalize the operational pattern used by the
runtime: load a compacted prefix state, then replay only the suffix:

```lean
-- Compaction/Props.lean:105-109
theorem snapshot_then_suffix_replay_eq_full_fold {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (compactedPrefix suffix : List alpha) :
    List.foldl step (List.foldl step init compactedPrefix) suffix =
      List.foldl step init (compactedPrefix ++ suffix) := by
  simpa using compaction_preserves_state step init compactedPrefix suffix
```

And the no-op case when no new suffix deltas exist:

```lean
-- Compaction/Props.lean:112-116
theorem snapshot_cutover_idempotent_without_new_suffix {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (compactedPrefix : List alpha) :
    List.foldl step (List.foldl step init compactedPrefix) [] =
      List.foldl step init compactedPrefix := by
  simp
```

The entire compaction proof machinery is built on `List.foldl_append` and
`List.take_append_drop` from the standard library. No commutativity or
associativity of the merge function is needed -- these are properties of `foldl`
itself. This means compaction correctness holds even for merge functions that
are not commutative (i.e., the guarantees apply during the compaction process
itself, independent of convergence).

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

The table composition proofs propagate this precondition through
`ValidTableRowPair` and `ValidTableRowTriple`, which bundle LWW consistency
for each LWW column alongside OR-Set canonicalization cleanness. This propagation
is the formal analogue of the runtime's invariant maintenance: each write assigns
a unique `(hlc, site)` pair, and each merge canonicalizes OR-Set output.

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
-- Compaction/Props.lean:36-45
theorem compaction_preserves_state {alpha beta : Type}
    (step : beta -> alpha -> beta) (init : beta) (preOps postOps : List alpha) :
    List.foldl step (List.foldl step init preOps) postOps =
      List.foldl step init (preOps ++ postOps) := by
  exact (List.foldl_append ...).symm
```

This is `List.foldl_append` from the standard library, applied in reverse. The
entire compaction proof machinery is an elegant wrapper around this single fact:
splitting a fold at any point and resuming is the same as folding the whole list.
The per-CRDT specializations (PN-Counter, OR-Set, MV-Register, LWW) and the
snapshot cutover laws are all direct applications of this core lemma with
type-specific instantiations.

### Table Operator Commutativity via Definitional Equality

The six operator commutativity theorems in the Table module
(`apply_counter_preserves_visibility`, `row_exists_counter_commute`, etc.) all
share the same proof pattern: `cases row; rfl`. This works because after
destructuring the row into its five fields, the two sides of the equation
become definitionally equal -- Lean can verify them by computation alone,
without any rewriting. This is a consequence of the table operations being
pure field updates that do not interact across columns.

```lean
-- Table/Props.lean:189-197
theorem row_exists_counter_commute
    (row : TableRowState alpha beta gamma Hlc)
    (existsEvent : LwwRegister Bool)
    (counterDelta : PnCounter)
    : applyCounterCell (applyRowExists row existsEvent) counterDelta =
      applyRowExists (applyCounterCell row counterDelta) existsEvent := by
  cases row
  rfl
```

### Disjoint Key Commutativity via calc

The `modify_row_at_disjoint_commute` theorem is the most involved table proof,
establishing that updates at distinct keys `k1 != k2` commute at the whole-table
level. The proof uses `funext` to reason pointwise about each key `current`, then
case-splits on whether `current = k1` or `current = k2`:

```lean
-- Table/Props.lean:225-248
theorem modify_row_at_disjoint_commute
    (table : TableState kappa alpha beta gamma Hlc)
    (k1 k2 : kappa) (hNe : k1 != k2)
    (f g : TableRowState alpha beta gamma Hlc -> TableRowState alpha beta gamma Hlc)
    : modifyRowAt (modifyRowAt table k1 f) k2 g =
      modifyRowAt (modifyRowAt table k2 g) k1 f := by
  funext current
  by_cases hCurrentK1 : current = k1
  . have hCurrentNeK2 : current != k2 := by
      intro hCurrentK2; apply hNe
      calc k1 = current := hCurrentK1.symm
           _ = k2 := hCurrentK2
    simp [modifyRowAt, hCurrentK1, hNe]
  . by_cases hCurrentK2 : current = k2
    . ...
    . simp [modifyRowAt, hCurrentK1, hCurrentK2]
```

The `calc` chain in the first branch is worth noting: it derives `k1 = k2` from
`current = k1` and `current = k2`, contradicting `hNe`. This is a common Lean
pattern for proving disjointness of key-indexed operations.

---

## Proof Architecture Summary

The proof architecture follows a clear layering strategy:

1. **Foundation layer** (HLC): Establish that `compareWithSite` is a strict total
   order with antisymmetry, transitivity, and reflexivity. All proofs here are
   direct natural number reasoning. (19 theorems)

2. **CRDT layer**: Each CRDT type proves its own semilattice triple (comm, assoc,
   idem). The techniques vary by type:
   - **LWW**: Case analysis on comparison results + HLC order properties + event-consistency
   - **PN-Counter**: Extensionality + `Nat.max` properties
   - **OR-Set**: Finset algebra + `aesop` + canonicalization chain
   - **MV-Register**: Finset union algebra
   (16 theorems)

3. **Table composition layer**: Proves that composite rows preserve semilattice
   properties under validity predicates (`ValidTableRowPair`, `ValidTableRowTriple`),
   lifts row-level proofs to whole-table via `funext`, and establishes operator
   commutativity for independent columns and disjoint keys. (16 theorems)

4. **Convergence layer**: Takes the per-CRDT semilattice proofs and composes them
   with the permutation-invariance of foldl to prove system-wide convergence. The
   key bridge is constructing `RightCommutative` from `comm + assoc`. (9 theorems)

5. **Compaction layer**: Proves that fold splitting is lossless via
   `List.foldl_append`, with per-CRDT specializations and snapshot cutover laws.
   (9 theorems)

6. **Application layer** (Tombstone, SQL, Replication): Derives domain-specific
   consequences. Tombstones reuse LWW proofs directly. SQL proofs use `decide` and
   boolean reflection. Replication proves cursor safety and compaction exclusion.
   (14 theorems)

The total proof codebase is approximately 1000 lines of proof text spread across
12 `Props.lean` files, covering 76+ theorems. Every theorem has a docstring, and
the proofs are readable enough to serve as documentation of the system's
correctness invariants. The table composition and OR-Set idempotence chain
represent the most recent additions, closing the gap between per-CRDT correctness
and the composite row/table level that the actual runtime operates on.
