import CrdtBase.Hlc.Defs

set_option autoImplicit false

namespace CrdtBase

/-- A Last-Writer-Wins register. -/
structure LwwRegister (α : Type) where
  val  : α
  hlc  : Hlc
  site : String
  deriving Repr, DecidableEq

namespace LwwRegister

/-- Merge two LWW registers. Higher (hlc, site) wins. -/
def merge {α : Type} (a b : LwwRegister α) : LwwRegister α :=
  match Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) with
  | .lt => b
  | .eq | .gt => a

end LwwRegister

end CrdtBase
