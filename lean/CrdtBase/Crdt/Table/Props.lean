import CrdtBase.Crdt.Table.Defs

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
