# Lean 4 Formal Verification Model

Formal specification and proofs for CRDTBase's core algorithms, following Cedar's verification-guided development approach: a readable Lean model serves as both the mathematical specification and the test oracle for the TypeScript implementation.

## Prior Art

This work builds directly on established formal verification of CRDTs:

- **Kleppmann et al. (OOPSLA 2017)**: [crdt-isabelle](https://github.com/trvedata/crdt-isabelle) — Isabelle/HOL framework proving Strong Eventual Consistency for OR-Set, Increment-Decrement Counter, and Replicated Growable Array. Defines the abstract convergence theorem we will port to Lean 4.
- **lean-yjs (iasakura)**: [lean-yjs](https://github.com/iasakura/lean-yjs) — Lean 4 verification of Yjs CRDT integration algorithm, proving preservation and commutativity. Demonstrates feasibility of CRDT proofs in Lean 4 specifically.
- **mlavrent/verified-crdt**: Lean 4 CRDT verification based on Burckhardt et al.'s framework (doi:10.1145/2535838.2535848).
- **Cedar (AWS)**: [cedar-spec](https://github.com/cedar-policy/cedar-spec) — Production verification-guided development: Lean 4 model + proofs + differential random testing against Rust implementation. Our TypeScript project follows this exact methodology.

---

## What We Verify (and Why)

### Tier 1: CRDT Merge Correctness (Critical)

Every CRDT merge function must form a **join-semilattice**: commutative, associative, idempotent. If any of these fail, replicas can permanently diverge — the fundamental guarantee of the system is broken.

For LWW specifically, this is true only under an event-consistency invariant: if two states have equal `(hlc, site)`, they must represent the same write event (same payload). Our current LWW merge is intentionally left-biased on exact key ties.

**Why formal proof and not just property tests:** Property tests generate millions of random inputs but can miss corner cases in comparison logic (e.g., tiebreaking when HLC and counter are equal but site IDs have specific ordinal relationships). Kleppmann's paper documents CRDTs that shipped with "proofs" that were later shown incorrect. A mechanized proof eliminates this class of error entirely.

Theorems for each CRDT type:
- `lww_merge_comm_of_consistent`: commutativity under the event-consistency invariant
- `lww_merge_assoc_of_consistent`: associativity under the event-consistency invariant
- `lww_merge_idem`: `merge(a, a) = a`
- Same three for `pn_counter_merge`, `or_set_merge`, `mv_register_merge`

OR-Set canonicalization properties are also proven to lock tombstone semantics:
- `or_set_canonicalize_idem`
- `or_set_canonicalize_no_tombstoned_tags`
- `or_set_canonicalize_preserves_visible_values`

**12 theorems total.** These are the non-negotiable core.

### Tier 2: HLC Ordering (Critical)

The HLC must provide a **strict total order** that is consistent with causality. If the ordering is wrong, LWW picks the wrong winner and data is silently corrupted.

Theorems:
- `hlc_total_order`: For any two HLCs `a` and `b`, exactly one of `a < b`, `a = b`, or `a > b` holds.
- `hlc_pack_preserves_order`: `wallMs₁ > wallMs₂ → pack(wallMs₁, c₁) > pack(wallMs₂, c₂)` for any counters `c₁`, `c₂`. (Wall clock dominates.)
- `hlc_counter_breaks_tie`: `pack(w, c₁) > pack(w, c₂) ↔ c₁ > c₂`. (Counter breaks ties within same millisecond.)
- `hlc_now_monotonic`: The `now()` function always returns an HLC strictly greater than the previous one from the same site.
- `hlc_recv_monotonic`: After `recv(remote)`, the local HLC is strictly greater than both the previous local HLC and the remote HLC.
- `hlc_site_tiebreak_total`: The extended comparison `(hlc, siteId)` is a total order. (Lexicographic site ID breaks equal HLCs.)

**6 theorems.**

### Operational Invariants (Assumptions We Must Enforce)

These are not "nice-to-have"; they are required for the LWW theorems to match production behavior:

- `siteId` uniqueness: each replica has a stable, globally unique site ID.
- Per-site monotonic clock: each new local write uses an HLC strictly greater than prior local writes.
- Durable clock state: the last emitted HLC is persisted and restored across restart/snapshot recovery.
- Event immutability: identical operation identity `(table, key, col, site, hlc)` cannot carry different payloads.

How this can fail in practice:

- Cloned configs or disk images reusing site IDs.
- Crash/restart paths that lose persisted HLC state.
- Rollback to old VM/container snapshots without fencing.
- Corrupt imports/replays that inject conflicting payloads for the same `(site, hlc)`.

Additional theorem targets to make these assumptions explicit:

- `lww_equal_key_implies_equal_payload` (or equivalent consistency predicate).
- `lww_merge_comm_of_consistent` and `lww_merge_assoc_of_consistent`.
- `hlc_now_strict_monotonic` and `hlc_recv_strict_monotonic` across state transitions.
- `dedup_rejects_conflicting_same_key` for ingest-level conflict checks.

### Tier 3: Convergence (The Crown Jewel)

The abstract convergence theorem, ported from Kleppmann's Isabelle framework: given a set of operations delivered in any order to any number of replicas, if each replica applies them using our merge functions, all replicas converge to identical state.

This is the theorem that says "the whole system works." It composes Tier 1 (merge is a semilattice) with a network model (messages can be reordered, duplicated, or delayed, but not permanently lost).

Theorems:
- `convergence_lww`: For any two replicas that have received the same set of LWW operations (in any order), their states are equal, assuming the operational invariants above.
- `convergence_pn_counter`: Same for PN-Counter. (Note: requires that operations are deduplicated by `(site, hlc)` — this is a precondition, not something the merge itself guarantees.)
- `convergence_or_set`: Same for OR-Set.
- `convergence_mv_register`: Same for MV-Register.
- `convergence_composite`: For a row with multiple columns of mixed CRDT types, convergence holds column-wise.

**5 theorems.**

### Tier 4: Compaction Correctness (Important)

Compaction must not lose or corrupt data. The key invariant: reading through compacted segments + post-compaction deltas must yield the same state as reading all original deltas.

Theorems:
- `compaction_preserves_state`: For any set of operations `ops`, partitioning them into `compacted_ops` and `remaining_ops` where `compacted_state = fold merge empty compacted_ops`: `fold merge compacted_state remaining_ops = fold merge empty ops`. In other words, partially pre-merging a prefix doesn't change the final result. (This follows from associativity and commutativity, but the proof makes the compaction-specific preconditions explicit.)
- `compaction_idempotent`: Compacting an already-compacted segment with no new deltas produces an identical segment.

**2 theorems.**

### Tier 5: Tombstone Consistency (Important)

Deletion is modeled as a LWW register on a hidden `_deleted` column. The interaction between deletes and concurrent writes needs to be precise.

Theorems:
- `delete_wins_if_later`: If a delete has a higher HLC than any concurrent write, the row is tombstoned in the merged state.
- `write_resurrects_if_later`: If a write has a higher HLC than a delete, the row is NOT tombstoned. (This is the intended semantic — LWW means last-writer-wins, including for deletes.)
- `tombstone_stable_without_new_writes`: Once a row is tombstoned and no new writes arrive, it remains tombstoned through any number of merges. (Idempotency of LWW applied to the `_deleted` column.)

**3 theorems.**

### Tier 6: SQL Translation + Planner + Evaluator Soundness (Important)

The SQL frontend is split into parser and semantics:

- **Parser:** handled in TypeScript property tests (`parse/print/parse` stability).
- **Semantics:** modeled in Lean as AST-to-CRDT-op translation, SELECT planning, and AST evaluation over SQL eval state (`result + nextState`).

The core guarantee for writes is that valid SQL write statements compile only to
syncable CRDT operations with schema-correct CRDT tags. This is the
"no accidental non-sync compilation" property.

The core guarantee for reads is that planner routing is deterministic:
- if `WHERE` contains `partition_by = value`, route to that single partition and
  remove exactly that routing predicate from residual filters;
- otherwise route to `all_partitions` and preserve all filters.

Initial theorem targets:
- `write_ops_type_sound`
- `write_ops_syncable`
- `no_nonsync_for_valid_crdt_writes`
- `planner_partition_sound`
- `planner_filter_preservation`

Evaluator parity currently relies on differential tests (`sql_eval`) against the TypeScript evaluator and is designed so future end-to-end SQL semantic theorems can be added without changing the wire protocol.

### What We Do NOT Verify

- **SQL parsing**: Syntax processing, not semantic correctness. Property tests are sufficient (round-trip: `parse(print(ast)) = ast`).
- **Binary encoding**: MessagePack encode/decode round-trip is a property test. The encoding has no semantic content that benefits from formal proof.
- **Storage adapters**: I/O code (OPFS, filesystem, S3). Untestable in Lean.
- **Network/sync protocol**: The sync protocol's correctness reduces to "deliver all operations eventually" + CRDT convergence. The former is an operational concern, the latter is Tier 3.
- **Bloom filter**: False-negative-freedom is a well-known property of the algorithm. Property test is sufficient.
- **Cross-table SQL optimization**: Join reordering, predicate pushdown, and cost-based optimization are out of scope for this SQL subset.

---

## Project Structure

Following Cedar's approach and Lean 4 conventions (lakefile.toml, standard Lake directory layout):

```
lean/
├── lakefile.toml
├── lean-toolchain
├── CrdtBase.lean                  # root import file
├── CrdtBase/
│   ├── Basic.lean                 # shared definitions, notation
│   │
│   ├── Hlc/
│   │   ├── Defs.lean              # HLC type, pack, unpack, now, recv
│   │   └── Props.lean             # HLC ordering theorems (Tier 2)
│   │
│   ├── Crdt/
│   │   ├── Lww/
│   │   │   ├── Defs.lean          # LWW register type and merge
│   │   │   └── Props.lean         # semilattice proofs (Tier 1)
│   │   ├── PnCounter/
│   │   │   ├── Defs.lean
│   │   │   └── Props.lean
│   │   ├── OrSet/
│   │   │   ├── Defs.lean
│   │   │   └── Props.lean
│   │   └── MvRegister/
│   │       ├── Defs.lean
│   │       └── Props.lean
│   │
│   ├── Convergence/
│   │   ├── Network.lean           # network model (message delivery axioms)
│   │   ├── Abstract.lean          # abstract convergence theorem
│   │   └── Concrete.lean          # per-type convergence (Tier 3)
│   │
│   ├── Compaction/
│   │   ├── Defs.lean              # compaction as fold-over-ops
│   │   └── Props.lean             # compaction correctness (Tier 4)
│   │
│   ├── Tombstone/
│   │   ├── Defs.lean              # delete model
│   │   └── Props.lean             # tombstone theorems (Tier 5)
│   │
│   ├── Sql/
│   │   ├── Defs.lean              # SQL AST subset + translation/planner/eval model
│   │   └── Props.lean             # SQL soundness proofs (Tier 6)
│   │
│   └── DiffTest/
│       └── Main.lean              # executable entry point for DRT
│
└── test/
    └── fixtures/                  # JSON test vectors shared with TypeScript
        ├── lww_merge_cases.json
        ├── hlc_order_cases.json
        └── ...
```

### lakefile.toml

```toml
[package]
name = "CrdtBase"
version = "0.1.0"
leanOptions = ["-DautoImplicit=false"]

[[lean_lib]]
name = "CrdtBase"

[[lean_exe]]
name = "CrdtBaseDRT"
root = "CrdtBase.DiffTest.Main"
```

`autoImplicit=false` is Cedar's convention and Mathlib's recommendation: all variables must be explicitly declared, preventing subtle type errors in theorems.

### Dependencies

Minimal. We do NOT depend on Mathlib (it's enormous and slow to build). Instead:

- **Batteries** (lean4 community standard library): Provides `HashMap`, `AssocList`, and basic tactics like `omega`, `simp`, `decide`. Much lighter than Mathlib.

If specific Mathlib lemmas are needed (e.g., about `Finset` or ordering), extract just those into local files rather than pulling the full dependency.

---

## Model Definitions

The Lean model is intentionally simpler than the TypeScript implementation. It uses natural Lean types (not MessagePack, not binary). The model is the *specification* — what the system *should* do. The TypeScript is the *implementation* — what the system *actually* does. Differential testing checks they agree.

### HLC

```lean
/-- A Hybrid Logical Clock timestamp. -/
structure Hlc where
  wallMs : Nat
  counter : Nat
  wallMs_lt : wallMs < 2 ^ 48
  counter_lt : counter < 2 ^ 16
  deriving Repr, DecidableEq

/-- Pack an HLC into a single natural number for comparison. -/
def Hlc.pack (h : Hlc) : Nat :=
  h.wallMs * 65536 + h.counter

/-- Construct an HLC only if both fields are within bounds. -/
def Hlc.mk? (wallMs counter : Nat) : Option Hlc := ...

/-- Total order on HLCs: compare packed values. -/
instance : Ord Hlc where
  compare a b := compare a.pack b.pack

/-- Extended comparison including site ID for tiebreaking. -/
def compareWithSite (a : Hlc × String) (b : Hlc × String) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | ord => ord
```

### LWW Register

```lean
/-- A Last-Writer-Wins register. -/
structure LwwRegister (α : Type) where
  val  : α
  hlc  : Hlc
  site : String
  deriving Repr, DecidableEq

/-- Merge two LWW registers. Higher (hlc, site) wins. -/
def LwwRegister.merge (a b : LwwRegister α) : LwwRegister α :=
  match compareWithSite (a.hlc, a.site) (b.hlc, b.site) with
  | .gt | .eq => a
  | .lt       => b
```

### PN-Counter

```lean
/-- A Positive-Negative Counter. Maps site IDs to increment/decrement counts. -/
structure PnCounter where
  inc : Batteries.HashMap String Nat
  dec : Batteries.HashMap String Nat
  deriving Repr

/-- Current value of a PN-Counter. -/
def PnCounter.value (c : PnCounter) : Int :=
  c.inc.values.foldl (· + ·) 0 - c.dec.values.foldl (· + ·) 0

/-- Merge: take pointwise max of each site's counts. -/
def PnCounter.merge (a b : PnCounter) : PnCounter where
  inc := mergeMaxMaps a.inc b.inc
  dec := mergeMaxMaps a.dec b.dec
```

### OR-Set

```lean
/-- An element in an OR-Set, tagged with its add-origin. -/
structure Tagged (α : Type) where
  val     : α
  addHlc  : Hlc
  addSite : String
  deriving Repr, DecidableEq

/-- An Observed-Remove Set. -/
structure OrSet (α : Type) where
  elements   : List (Tagged α)
  tombstones : List (Hlc × String)
  deriving Repr

/-- Merge: union elements and tombstones, then filter elements by tombstones. -/
def OrSet.merge (a b : OrSet α) : OrSet α where
  elements := ((a.elements ++ b.elements).dedup).filter (fun e =>
    !((a.tombstones ++ b.tombstones).dedup.contains (e.addHlc, e.addSite)))
  tombstones := (a.tombstones ++ b.tombstones).dedup
```

### Network Model

Following Kleppmann's approach: an axiomatic model of an asynchronous network where messages can be reordered, duplicated, and delayed, but are eventually delivered.

```lean
/-- A site's state is the result of applying a sequence of operations. -/
def applyOps (merge : σ → σ → σ) (init : σ) : List σ → σ :=
  List.foldl merge init

/-- Two sites have received the same operations (as a set) but possibly
    in different order. -/
structure SameOps (ops₁ ops₂ : List σ) : Prop where
  same_elements : ∀ x, x ∈ ops₁ ↔ x ∈ ops₂
```

---

## Proof Strategy

### Semilattice Proofs (Tier 1)

For each CRDT merge, prove three properties. The general strategy:

**Commutativity** — Case-split on the comparison result. For LWW: if `compareWithSite(a, b) = .gt` then `compareWithSite(b, a) = .lt`, so both orderings select `a`. The `eq` case requires the event-consistency invariant (`same (hlc,site)` implies same payload), since merge is left-biased on exact ties.

**Associativity** — The key insight: `merge` always selects one of its inputs (it's a "max" operation). For LWW, `merge(merge(a, b), c)` selects the maximum of `{a, b, c}` by `(hlc, site)`. Associativity follows from transitivity of the total order. Proving this requires:
1. `compareWithSite` is a total order (proven in Tier 2).
2. `merge` returns the greater of its two arguments under this order.
3. "Max of max(a,b) and c" equals "max of a and max(b,c)" — a standard property of max under a total order.

For PN-Counter, associativity of `mergeMaxMaps` reduces to `Nat.max` being associative (`max(max(a,b),c) = max(a,max(b,c))`), applied pointwise. This is in Batteries.

**Idempotency** — For LWW: `compare(a, a) = .eq`, so `merge(a, a) = a`. For PN-Counter: `Nat.max(n, n) = n`. For OR-Set: `dedup` on the union of identical lists.

### Convergence Proofs (Tier 3)

The abstract convergence theorem (from Kleppmann):

```lean
/-- If merge forms a join-semilattice and two sites have received
    the same set of operations, they converge to the same state. -/
theorem convergence
    (comm : ∀ a b, merge a b = merge b a)
    (assoc : ∀ a b c, merge (merge a b) c = merge a (merge b c))
    (idem : ∀ a, merge a a = a)
    (same : SameOps ops₁ ops₂)
    : applyOps merge init ops₁ = applyOps merge init ops₂ := by
  -- Proof: since merge is commutative and associative, foldl merge
  -- over any permutation of the same multiset yields the same result.
  -- This is the "essence" of why CRDTs converge.
  sorry -- to be filled in
```

The proof uses the fact that `foldl` over a commutative, associative operation is invariant under permutation. This is a standard result. If it exists in Batteries, use it; otherwise prove it (the induction is straightforward).

Each concrete convergence theorem (Tier 3) is then obtained by instantiating the abstract theorem with the specific merge function and its Tier 1 proofs.

### Compaction Proofs (Tier 4)

Compaction takes a prefix of operations and pre-merges them into a single state. The correctness proof:

```lean
/-- Compaction preserves the final merged state. -/
theorem compaction_preserves_state
    (assoc : ∀ a b c, merge (merge a b) c = merge a (merge b c))
    (comm : ∀ a b, merge a b = merge b a)
    (prefix suffix : List σ)
    : applyOps merge init (prefix ++ suffix)
    = applyOps merge (applyOps merge init prefix) suffix := by
  -- This is just the associativity of foldl, which follows from
  -- associativity of merge.
  sorry
```

This theorem directly justifies the compaction job's correctness: compacting `prefix` into a segment, then applying `suffix` (new deltas) on top, gives the same result as applying everything from scratch.

---

## Differential Testing Bridge

The Lean model is compiled to an executable (`CrdtBaseDRT`) that reads JSON test vectors from stdin and writes results to stdout. The TypeScript test harness:

1. Generates random inputs using `fast-check` (HLC values, CRDT states, operation sequences).
2. Serializes them as JSON.
3. Pipes them through the Lean executable.
4. Runs the same inputs through the TypeScript implementation.
5. Compares outputs.

### JSON Protocol

```json
// Input (one per line)
{"type":"lww_merge","a":{"val":"x","hlc":{"wallMs":1000,"counter":0},"site":"aaa"},"b":{"val":"y","hlc":{"wallMs":999,"counter":5},"site":"bbb"}}

// Output (one per line)
{"result":{"val":"x","hlc":{"wallMs":1000,"counter":0},"site":"aaa"}}
```

The Lean executable processes JSONL commands with shape:
- `{"type":"lww_merge", ... }`
- `{"type":"sql_generate_ops", "statement": <write-ast>, "context": <sql-context>}`
- `{"type":"sql_build_select_plan", "statement": <select-ast>, "schema": <planner-schema>}`
- `{"type":"sql_eval", "statement": <sql-ast>, "context": <eval-context>, "state": <eval-state>}`

`sql_generate_ops` and `sql_eval` use AST+context envelopes (not raw SQL text) to avoid parser duplication.

In tests, SQL is still generated as **text**; TypeScript parses once, then sends the same AST payload to Lean and the TS evaluator/planner for differential comparison.

`sql_build_select_plan` verifies the same planner routing/filter behavior used by TypeScript.

All command failures are returned as:

```json
{"error":"<message>"}
```

### Running DRT

```bash
# Build the Lean executable
cd lean && lake build CrdtBaseDRT

# Run differential tests (from TypeScript test suite)
cd .. && npx vitest run --filter drt
```

The TypeScript DRT test (in vitest) spawns the Lean executable as a child process, streams JSON lines to it, and compares outputs. fast-check generates the inputs, so each run exercises different random cases. CI runs this nightly with a high iteration count (100,000+).

---

## Implementation Order

### Phase A: Definitions Only (No Proofs)

Write all the `Defs.lean` files. Verify they compile and are executable. Write the DRT bridge (`DiffTest/Main.lean`). Connect to TypeScript test harness. At this point, you have a working reference implementation in Lean that serves as a test oracle, even before any proofs exist.

This is immediately useful: any divergence between Lean and TypeScript is a bug in one of them.

### Phase B: Tier 1 + 2 Proofs

Prove the semilattice properties for each CRDT merge. For LWW, phrase commutativity/associativity as conditional on the event-consistency invariant and prove that invariant is preserved by valid operation generation/ingest rules. Prove HLC ordering and monotonicity properties. These are the most valuable proofs per line of effort.

### Phase C: Tier 3 Proofs

Prove the abstract convergence theorem. Instantiate for each CRDT type. This is the theorem that lets you sleep at night.

### Phase D: Tier 4 + 5 Proofs

Prove compaction correctness and tombstone consistency. These follow relatively directly from the Tier 1 proofs.

---

## Style Guidelines

Follow Cedar's conventions (adapted from their [GUIDE.md](https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/GUIDE.md)):

- `autoImplicit=false` globally. All variables explicitly declared.
- Type variables: lower-case Greek (`α`, `σ`).
- Theorem names: `lower_snake_case` (e.g., `lww_merge_comm`).
- Types and structures: `UpperCamelCase` (e.g., `LwwRegister`, `PnCounter`).
- Constructors: `lowerCamelCase`.
- Use `simp only` instead of `simp` (except to close goals). This prevents proofs from breaking on Lean/Batteries upgrades.
- Use `exact` over `apply` when possible.
- Every theorem has a docstring `/-- ... -/` explaining what is proven in plain English.
- Imports sorted lexicographically, kept minimal.
- No Mathlib dependency. Batteries only.

---

## Estimated Effort

Based on Cedar's published data (1,673 lines model + 5,714 lines proofs for evaluator + validator + authorizer) and Kleppmann's experience (OR-Set and Counter proofs in "a few hours" each):

| Component | Model (LOC) | Proofs (LOC) | Estimated Time |
|-----------|-------------|-------------|----------------|
| HLC definitions + ordering | ~50 | ~100 | 1 day |
| LWW Register | ~30 | ~80 | 1 day |
| PN-Counter | ~50 | ~150 | 1-2 days |
| OR-Set | ~60 | ~200 | 2-3 days |
| MV-Register | ~30 | ~80 | 1 day |
| Network model | ~40 | ~0 | 0.5 days |
| Abstract convergence | ~20 | ~120 | 1-2 days |
| Concrete convergence (×4) | ~20 | ~80 | 1 day |
| Compaction | ~30 | ~60 | 0.5 days |
| Tombstones | ~20 | ~50 | 0.5 days |
| DRT bridge | ~100 | ~0 | 1 day |
| **Total** | **~450** | **~920** | **~10-13 days** |

The model is ~10x smaller than the TypeScript implementation, consistent with Cedar's ratio.
