import CrdtBase.Crdt.Table.Defs
import CrdtBase.Crdt.Lww.Props
import CrdtBase.Crdt.PnCounter.Props
import CrdtBase.Crdt.OrSet.Props
import CrdtBase.Crdt.MvRegister.Props

set_option autoImplicit false

namespace CrdtBase

section TableMerge

variable {κ α β γ Hlc : Type}
variable [DecidableEq β] [DecidableEq Hlc] [DecidableEq γ]

/-- Whole-table merge is commutative if row merge is commutative. -/
theorem table_merge_comm_of_row_comm
    (hRowComm : ∀ x y : TableRowState α β γ Hlc, mergeTableRow x y = mergeTableRow y x)
    (a b : TableState κ α β γ Hlc)
    : mergeTable a b = mergeTable b a := by
  funext key
  exact hRowComm (a key) (b key)

/-- Whole-table merge is associative if row merge is associative. -/
theorem table_merge_assoc_of_row_assoc
    (hRowAssoc : ∀ x y z : TableRowState α β γ Hlc,
      mergeTableRow (mergeTableRow x y) z = mergeTableRow x (mergeTableRow y z))
    (a b c : TableState κ α β γ Hlc)
    : mergeTable (mergeTable a b) c = mergeTable a (mergeTable b c) := by
  funext key
  exact hRowAssoc (a key) (b key) (c key)

/-- Whole-table merge is idempotent if row merge is idempotent. -/
theorem table_merge_idem_of_row_idem
    (hRowIdem : ∀ x : TableRowState α β γ Hlc, mergeTableRow x x = x)
    (a : TableState κ α β γ Hlc)
    : mergeTable a a = a := by
  funext key
  exact hRowIdem (a key)

end TableMerge

/-! ### Validity predicate and instantiated row-level CRDT theorems -/

section ValidTableRow

variable {α β γ Hlc : Type}
variable [DecidableEq β] [DecidableEq Hlc] [DecidableEq γ]

/-- A valid table row state requires LWW event-consistency between any two
    rows being merged (for the `alive` and `lwwCol` columns) and that the
    OR-Set column is canonicalized (no element tag appears in tombstones).

    This predicate captures the system-level invariant that:
    1. Each `(hlc, site)` pair uniquely determines the LWW payload
       (event-consistency), and
    2. OR-Set state has been canonicalized (as it always is after a merge). -/
structure ValidTableRowPair (a b : TableRowState α β γ Hlc) : Prop where
  alive_consistent   : LwwConsistentPair a.alive b.alive
  lwwCol_consistent  : LwwConsistentPair a.lwwCol b.lwwCol
  setCol_a_clean     : ∀ x ∈ a.setCol.elements, x.tag ∉ a.setCol.tombstones
  setCol_b_clean     : ∀ x ∈ b.setCol.elements, x.tag ∉ b.setCol.tombstones

/-- Row merge is commutative under the validity predicate, by case-splitting
    on each column's CRDT type and applying the appropriate per-type theorem. -/
theorem mergeTableRow_comm_of_valid
    (a b : TableRowState α β γ Hlc)
    (hValid : ValidTableRowPair a b)
    : mergeTableRow a b = mergeTableRow b a := by
  simp only [mergeTableRow, TableRowState.mk.injEq]
  exact ⟨lww_merge_comm_of_consistent a.alive b.alive hValid.alive_consistent,
         lww_merge_comm_of_consistent a.lwwCol b.lwwCol hValid.lwwCol_consistent,
         pn_counter_merge_comm a.counterCol b.counterCol,
         or_set_merge_comm a.setCol b.setCol,
         mv_register_merge_comm a.registerCol b.registerCol⟩

/-- Pairwise validity for three-way associativity proofs: event-consistency
    must hold for all LWW column pairs (a,b), (b,c). -/
structure ValidTableRowTriple (a b c : TableRowState α β γ Hlc) : Prop where
  alive_ab : LwwConsistentPair a.alive b.alive
  alive_bc : LwwConsistentPair b.alive c.alive
  lww_ab   : LwwConsistentPair a.lwwCol b.lwwCol
  lww_bc   : LwwConsistentPair b.lwwCol c.lwwCol

/-- Row merge is associative under pairwise LWW event-consistency. -/
theorem mergeTableRow_assoc_of_valid
    (a b c : TableRowState α β γ Hlc)
    (hValid : ValidTableRowTriple a b c)
    : mergeTableRow (mergeTableRow a b) c = mergeTableRow a (mergeTableRow b c) := by
  simp only [mergeTableRow, TableRowState.mk.injEq]
  exact ⟨lww_merge_assoc_of_consistent a.alive b.alive c.alive
           hValid.alive_ab hValid.alive_bc,
         lww_merge_assoc_of_consistent a.lwwCol b.lwwCol c.lwwCol
           hValid.lww_ab hValid.lww_bc,
         pn_counter_merge_assoc a.counterCol b.counterCol c.counterCol,
         or_set_merge_assoc a.setCol b.setCol c.setCol,
         mv_register_merge_assoc a.registerCol b.registerCol c.registerCol⟩

/-- Row merge is idempotent. LWW idempotence is unconditional; OR-Set
    idempotence requires canonicalization, which holds for any merge output
    (see `or_set_merge_canonicalized`).

    We require that each row's OR-Set column is canonicalized, which is
    automatically the case after any merge operation. -/
theorem mergeTableRow_idem_of_valid
    (a : TableRowState α β γ Hlc)
    (hSetClean : ∀ x ∈ a.setCol.elements, x.tag ∉ a.setCol.tombstones)
    : mergeTableRow a a = a := by
  cases a with | mk aAlive aLww aCounter aSet aReg =>
  simp only [mergeTableRow, TableRowState.mk.injEq]
  exact ⟨lww_merge_idem aAlive,
         lww_merge_idem aLww,
         pn_counter_merge_idem aCounter,
         or_set_merge_idem aSet hSetClean,
         mv_register_merge_idem aReg⟩

/-! ### Lifted whole-table theorems under validity -/

/-- Whole-table validity: every pair of rows satisfies the LWW consistency
    and OR-Set canonicalization invariants. -/
def ValidTableState {κ : Type} (a b : TableState κ α β γ Hlc) : Prop :=
  ∀ key : κ, ValidTableRowPair (a key) (b key)

/-- Whole-table merge is commutative under validity. -/
theorem mergeTable_comm_of_valid {κ : Type}
    (a b : TableState κ α β γ Hlc)
    (hValid : ValidTableState a b)
    : mergeTable a b = mergeTable b a := by
  funext key
  exact mergeTableRow_comm_of_valid (a key) (b key) (hValid key)

/-- Whole-table triple validity: pairwise LWW consistency for all rows. -/
def ValidTableStateTriple {κ : Type} (a b c : TableState κ α β γ Hlc) : Prop :=
  ∀ key : κ, ValidTableRowTriple (a key) (b key) (c key)

/-- Whole-table merge is associative under pairwise validity. -/
theorem mergeTable_assoc_of_valid {κ : Type}
    (a b c : TableState κ α β γ Hlc)
    (hValid : ValidTableStateTriple a b c)
    : mergeTable (mergeTable a b) c = mergeTable a (mergeTable b c) := by
  funext key
  exact mergeTableRow_assoc_of_valid (a key) (b key) (c key) (hValid key)

/-- Whole-table idempotence validity: every row's OR-Set is canonicalized. -/
def ValidTableStateIdem {κ : Type} (a : TableState κ α β γ Hlc) : Prop :=
  ∀ key : κ, ∀ x ∈ (a key).setCol.elements, x.tag ∉ (a key).setCol.tombstones

/-- Whole-table merge is idempotent under OR-Set canonicalization. -/
theorem mergeTable_idem_of_valid {κ : Type}
    (a : TableState κ α β γ Hlc)
    (hValid : ValidTableStateIdem a)
    : mergeTable a a = a := by
  funext key
  exact mergeTableRow_idem_of_valid (a key) (hValid key)

end ValidTableRow

section OperatorComposition

variable {α β γ Hlc : Type}

/-- Counter updates do not change row visibility. -/
theorem apply_counter_preserves_visibility
    (row : TableRowState α β γ Hlc)
    (counterDelta : PnCounter)
    : rowVisible (applyCounterCell row counterDelta) = rowVisible row := by
  cases row
  rfl

/-- OR-Set updates do not change row visibility. -/
theorem apply_set_preserves_visibility
    [DecidableEq β] [DecidableEq Hlc]
    (row : TableRowState α β γ Hlc)
    (setDelta : OrSet β Hlc)
    : rowVisible (applySetCell row setDelta) = rowVisible row := by
  cases row
  rfl

/-- MV-register updates do not change row visibility. -/
theorem apply_register_preserves_visibility
    [DecidableEq γ]
    (row : TableRowState α β γ Hlc)
    (registerDelta : MvRegister γ)
    : rowVisible (applyRegisterCell row registerDelta) = rowVisible row := by
  cases row
  rfl

/-- Row-existence updates commute with counter updates (independent columns). -/
theorem row_exists_counter_commute
    (row : TableRowState α β γ Hlc)
    (existsEvent : LwwRegister Bool)
    (counterDelta : PnCounter)
    : applyCounterCell (applyRowExists row existsEvent) counterDelta =
      applyRowExists (applyCounterCell row counterDelta) existsEvent := by
  cases row
  rfl

/-- Row-existence updates commute with OR-Set updates (independent columns). -/
theorem row_exists_set_commute
    [DecidableEq β] [DecidableEq Hlc]
    (row : TableRowState α β γ Hlc)
    (existsEvent : LwwRegister Bool)
    (setDelta : OrSet β Hlc)
    : applySetCell (applyRowExists row existsEvent) setDelta =
      applyRowExists (applySetCell row setDelta) existsEvent := by
  cases row
  rfl

/-- Counter and MV-register updates commute (independent columns). -/
theorem row_counter_register_commute
    [DecidableEq γ]
    (row : TableRowState α β γ Hlc)
    (counterDelta : PnCounter)
    (registerDelta : MvRegister γ)
    : applyRegisterCell (applyCounterCell row counterDelta) registerDelta =
      applyCounterCell (applyRegisterCell row registerDelta) counterDelta := by
  cases row
  rfl

section DisjointKeys

variable {κ : Type} [DecidableEq κ]

/-- Updates at disjoint keys commute at whole-table level. -/
theorem modify_row_at_disjoint_commute
    (table : TableState κ α β γ Hlc)
    (k1 k2 : κ)
    (hNe : k1 ≠ k2)
    (f g : TableRowState α β γ Hlc → TableRowState α β γ Hlc)
    : modifyRowAt (modifyRowAt table k1 f) k2 g =
      modifyRowAt (modifyRowAt table k2 g) k1 f := by
  funext current
  by_cases hCurrentK1 : current = k1
  · have hCurrentNeK2 : current ≠ k2 := by
      intro hCurrentK2
      apply hNe
      calc
        k1 = current := hCurrentK1.symm
        _ = k2 := hCurrentK2
    simp [modifyRowAt, hCurrentK1, hNe]
  · by_cases hCurrentK2 : current = k2
    · have hCurrentNeK1 : current ≠ k1 := by
        exact hCurrentK1
      have hK2NeK1 : k2 ≠ k1 := by
        intro h
        exact hNe h.symm
      simp [modifyRowAt, hCurrentK2, hK2NeK1]
    · simp [modifyRowAt, hCurrentK1, hCurrentK2]

end DisjointKeys

end OperatorComposition

end CrdtBase
