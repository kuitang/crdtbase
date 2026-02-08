set_option autoImplicit false

namespace CrdtBase

/-- A Positive-Negative counter state as pointwise site counts. -/
structure PnCounter where
  inc : String → Nat
  dec : String → Nat

@[ext] theorem PnCounter.ext
    {a b : PnCounter}
    (hInc : ∀ site, a.inc site = b.inc site)
    (hDec : ∀ site, a.dec site = b.dec site) :
    a = b := by
  cases a with
  | mk aInc aDec =>
      cases b with
      | mk bInc bDec =>
          have hIncEq : aInc = bInc := funext hInc
          have hDecEq : aDec = bDec := funext hDec
          cases hIncEq
          cases hDecEq
          rfl

namespace PnCounter

/-- Merge uses pointwise max for both increment and decrement maps. -/
@[simp]
def merge (a b : PnCounter) : PnCounter :=
  { inc := fun site => max (a.inc site) (b.inc site)
    dec := fun site => max (a.dec site) (b.dec site) }

end PnCounter

end CrdtBase
