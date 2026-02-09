import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

namespace CrdtBase

namespace Convergence

/-- Apply an operation stream to a state. -/
def applyOps {σ α : Type} (step : σ → α → σ) (init : σ) (ops : List α) : σ :=
  List.foldl step init ops

/-- Two streams contain the same operations up to permutation. -/
structure SameOps {α : Type} (ops₁ ops₂ : List α) : Prop where
  perm : List.Perm ops₁ ops₂

end Convergence

end CrdtBase
