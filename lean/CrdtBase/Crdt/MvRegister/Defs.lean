import CrdtBase.Hlc.Defs
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

namespace CrdtBase

/-- A value/version entry in an MV-register. -/
structure MvValue (α : Type) where
  val  : α
  hlc  : Hlc
  site : String
  deriving Repr, DecidableEq

/-- A Multi-Value register state. -/
structure MvRegister (α : Type) where
  values : Finset (MvValue α)

@[ext] theorem MvRegister.ext {α : Type} {a b : MvRegister α}
    (hValues : a.values = b.values) : a = b := by
  cases a
  cases b
  cases hValues
  rfl

namespace MvRegister

/-- Merge is set union of observed values. -/
@[simp]
def merge {α : Type} [DecidableEq α] (a b : MvRegister α) : MvRegister α :=
  { values := a.values ∪ b.values }

end MvRegister

end CrdtBase
