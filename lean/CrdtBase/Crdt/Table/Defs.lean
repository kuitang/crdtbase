import CrdtBase.Crdt.Lww.Defs
import CrdtBase.Crdt.PnCounter.Defs
import CrdtBase.Crdt.OrSet.Defs
import CrdtBase.Crdt.MvRegister.Defs

set_option autoImplicit false

namespace CrdtBase

/-- A composite row CRDT: row visibility + mixed column CRDT states. -/
structure TableRowState (α β γ Hlc : Type) where
  alive : LwwRegister Bool
  lwwCol : LwwRegister α
  counterCol : PnCounter
  setCol : OrSet β Hlc
  registerCol : MvRegister γ

/-- Componentwise row merge across mixed CRDT columns. -/
def mergeTableRow {α β γ Hlc : Type} [DecidableEq β] [DecidableEq Hlc] [DecidableEq γ]
    (a b : TableRowState α β γ Hlc) : TableRowState α β γ Hlc :=
  {
    alive := LwwRegister.merge a.alive b.alive
    lwwCol := LwwRegister.merge a.lwwCol b.lwwCol
    counterCol := PnCounter.merge a.counterCol b.counterCol
    setCol := OrSet.merge a.setCol b.setCol
    registerCol := MvRegister.merge a.registerCol b.registerCol
  }

/-- Whole-table state: a map from key to row-state. -/
abbrev TableState (κ α β γ Hlc : Type) := κ → TableRowState α β γ Hlc

/-- Whole-table merge is pointwise row merge. -/
def mergeTable {κ α β γ Hlc : Type} [DecidableEq β] [DecidableEq Hlc] [DecidableEq γ]
    (a b : TableState κ α β γ Hlc) : TableState κ α β γ Hlc :=
  fun key => mergeTableRow (a key) (b key)

/-- Visibility projection for reads. -/
def rowVisible {α β γ Hlc : Type} (row : TableRowState α β γ Hlc) : Bool :=
  row.alive.val

/-- Row op: merge an incoming row-existence event. -/
def applyRowExists {α β γ Hlc : Type}
    (row : TableRowState α β γ Hlc)
    (incoming : LwwRegister Bool) : TableRowState α β γ Hlc :=
  { row with alive := LwwRegister.merge row.alive incoming }

/-- Row op: merge an incoming LWW cell event. -/
def applyLwwCell {α β γ Hlc : Type}
    (row : TableRowState α β γ Hlc)
    (incoming : LwwRegister α) : TableRowState α β γ Hlc :=
  { row with lwwCol := LwwRegister.merge row.lwwCol incoming }

/-- Row op: merge an incoming PN-counter fragment. -/
def applyCounterCell {α β γ Hlc : Type}
    (row : TableRowState α β γ Hlc)
    (incoming : PnCounter) : TableRowState α β γ Hlc :=
  { row with counterCol := PnCounter.merge row.counterCol incoming }

/-- Row op: merge an incoming OR-Set fragment. -/
def applySetCell {α β γ Hlc : Type} [DecidableEq β] [DecidableEq Hlc]
    (row : TableRowState α β γ Hlc)
    (incoming : OrSet β Hlc) : TableRowState α β γ Hlc :=
  { row with setCol := OrSet.merge row.setCol incoming }

/-- Row op: merge an incoming MV-register fragment. -/
def applyRegisterCell {α β γ Hlc : Type} [DecidableEq γ]
    (row : TableRowState α β γ Hlc)
    (incoming : MvRegister γ) : TableRowState α β γ Hlc :=
  { row with registerCol := MvRegister.merge row.registerCol incoming }

/-- Functional row update at a specific key. -/
def modifyRowAt {κ α β γ Hlc : Type} [DecidableEq κ]
    (table : TableState κ α β γ Hlc)
    (key : κ)
    (f : TableRowState α β γ Hlc → TableRowState α β γ Hlc)
    : TableState κ α β γ Hlc :=
  fun current => if current = key then f (table current) else table current

end CrdtBase
