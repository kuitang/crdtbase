import CrdtBase.Crdt.Lww.Defs
import CrdtBase.Crdt.PnCounter.Defs
import CrdtBase.Crdt.OrSet.Defs
import CrdtBase.Crdt.MvRegister.Defs

set_option autoImplicit false

namespace CrdtBase

namespace Compaction

/-- Apply a split compaction strategy: fold `take split`, then continue with `drop split`. -/
def foldPrefixSuffix {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) (split : Nat) : β :=
  List.foldl step (List.foldl step init (ops.take split)) (ops.drop split)

/-- Empty PN-counter state used as a compaction base. -/
def pnCounterEmpty : PnCounter :=
  { inc := fun _ => 0
    dec := fun _ => 0 }

/-- Empty OR-Set state used as a compaction base. -/
def orSetEmpty (α Hlc : Type) : OrSet α Hlc :=
  { elements := ∅
    tombstones := ∅ }

/-- Empty MV-register state used as a compaction base. -/
def mvRegisterEmpty (α : Type) : MvRegister α :=
  { values := ∅ }

/-- LWW compaction step using `Option` to represent an empty starting state. -/
def lwwStep {α : Type}
    (state : Option (LwwRegister α)) (next : LwwRegister α) : Option (LwwRegister α) :=
  match state with
  | none => some next
  | some current => some (LwwRegister.merge current next)

end Compaction

end CrdtBase
