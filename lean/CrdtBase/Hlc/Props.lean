import Batteries
import CrdtBase.Hlc.Defs

namespace CrdtBase

open Hlc

/-- recv rejects remote timestamps that drift too far into the future. -/
theorem recv_none_of_drift
    (local remote : Hlc)
    (now : Nat)
    (hDrift : remote.wallMs > now + driftLimitMs)
    : Hlc.recv local remote now = none := by
  simp [Hlc.recv, hDrift]

/-- Any successful recv result remains within the declared bounds. -/
theorem recv_some_bounds
    (local remote : Hlc)
    (now : Nat)
    (out : Hlc)
    (h : Hlc.recv local remote now = some out)
    : out.wallMs < wallMsMax ∧ out.counter < counterMax := by
  exact ⟨out.wallMs_lt, out.counter_lt⟩

/-- Any successful now result remains within the declared bounds. -/
theorem now_some_bounds
    (local : Hlc)
    (wall : Nat)
    (out : Hlc)
    (h : Hlc.now local wall = some out)
    : out.wallMs < wallMsMax ∧ out.counter < counterMax := by
  exact ⟨out.wallMs_lt, out.counter_lt⟩

/-- max3 dominates each of its arguments. -/
theorem max3_ge_left (a b c : Nat) : a ≤ Hlc.max3 a b c := by
  simp [Hlc.max3, Nat.le_max_left]

/-- max3 dominates each of its arguments (middle). -/
theorem max3_ge_mid (a b c : Nat) : b ≤ Hlc.max3 a b c := by
  simp [Hlc.max3, Nat.le_max_right, Nat.le_max_left]

/-- max3 dominates each of its arguments (right). -/
theorem max3_ge_right (a b c : Nat) : c ≤ Hlc.max3 a b c := by
  simp [Hlc.max3, Nat.le_max_right]

/-- If recv succeeds, the resulting wallMs is at least every input clock. -/
theorem recv_wallMs_monotonic
    (local remote : Hlc)
    (now : Nat)
    (out : Hlc)
    (h : Hlc.recv local remote now = some out)
    : local.wallMs ≤ out.wallMs ∧ remote.wallMs ≤ out.wallMs ∧ now ≤ out.wallMs := by
  -- recvWall is max3 of the three inputs, and mk? preserves wallMs.
  have hWall : out.wallMs = Hlc.recvWall local remote now := by
    -- unfold and simplify the mk? branch selected by h.
    simp [Hlc.recv, Hlc.recvWall, Hlc.recvCounter, Hlc.mk?] at h
    -- simp leaves the resulting wallMs equality in the goal.
    exact h
  constructor
  · simpa [hWall] using (max3_ge_left local.wallMs remote.wallMs now)
  constructor
  · simpa [hWall] using (max3_ge_mid local.wallMs remote.wallMs now)
  · simpa [hWall] using (max3_ge_right local.wallMs remote.wallMs now)

end CrdtBase
