import Batteries
import CrdtBase.Hlc.Defs

namespace CrdtBase

open Hlc

/-- recv rejects remote timestamps that drift too far into the future. -/
theorem recv_none_of_drift
    (localHlc remote : Hlc)
    (now : Nat)
    (hDrift : remote.wallMs > now + driftLimitMs)
    : Hlc.recv localHlc remote now = none := by
  simp [Hlc.recv, hDrift]

/-- Any successful recv result remains within the declared bounds. -/
theorem recv_some_bounds
    (localHlc remote : Hlc)
    (now : Nat)
    (out : Hlc)
    (h : Hlc.recv localHlc remote now = some out)
    : out.wallMs < wallMsMax ∧ out.counter < counterMax := by
  exact ⟨out.wallMs_lt, out.counter_lt⟩

/-- Any successful now result remains within the declared bounds. -/
theorem now_some_bounds
    (localHlc : Hlc)
    (wall : Nat)
    (out : Hlc)
    (h : Hlc.now localHlc wall = some out)
    : out.wallMs < wallMsMax ∧ out.counter < counterMax := by
  exact ⟨out.wallMs_lt, out.counter_lt⟩

/-- max3 dominates each of its arguments. -/
theorem max3_ge_left (a b c : Nat) : a ≤ Hlc.max3 a b c := by
  simp [Hlc.max3, Nat.le_max_left]

/-- max3 dominates each of its arguments (middle). -/
theorem max3_ge_mid (a b c : Nat) : b ≤ Hlc.max3 a b c := by
  have hbc : b ≤ max b c := Nat.le_max_left b c
  have habc : max b c ≤ max a (max b c) := Nat.le_max_right a (max b c)
  exact Nat.le_trans hbc habc

/-- max3 dominates each of its arguments (right). -/
theorem max3_ge_right (a b c : Nat) : c ≤ Hlc.max3 a b c := by
  have hbc : c ≤ max b c := Nat.le_max_right b c
  have habc : max b c ≤ max a (max b c) := Nat.le_max_right a (max b c)
  exact Nat.le_trans hbc habc

/-- If recv succeeds, the resulting wallMs is at least every input clock. -/
theorem recv_wallMs_monotonic
    (localHlc remote : Hlc)
    (now : Nat)
    (out : Hlc)
    (h : Hlc.recv localHlc remote now = some out)
    : localHlc.wallMs ≤ out.wallMs ∧ remote.wallMs ≤ out.wallMs ∧ now ≤ out.wallMs := by
  have hRecv :
      remote.wallMs ≤ now + driftLimitMs ∧
      ∃ hWall hCounter,
        { wallMs := Hlc.max3 localHlc.wallMs remote.wallMs now
          , counter :=
              if Hlc.max3 localHlc.wallMs remote.wallMs now = localHlc.wallMs then
                if Hlc.max3 localHlc.wallMs remote.wallMs now = remote.wallMs then
                  max localHlc.counter remote.counter + 1
                else
                  localHlc.counter + 1
              else if Hlc.max3 localHlc.wallMs remote.wallMs now = remote.wallMs then
                remote.counter + 1
              else
                0
          , wallMs_lt := hWall
          , counter_lt := hCounter
          } = out := by
    simpa [Hlc.recv, Hlc.recvWall, Hlc.recvCounter, Hlc.mk?] using h
  rcases hRecv with ⟨_, ⟨_, _, hEq⟩⟩
  have hWallRaw : Hlc.max3 localHlc.wallMs remote.wallMs now = out.wallMs := by
    simpa using congrArg Hlc.wallMs hEq
  have hWall : out.wallMs = Hlc.recvWall localHlc remote now := by
    simpa [Hlc.recvWall] using hWallRaw.symm
  constructor
  · simpa [hWall] using (max3_ge_left localHlc.wallMs remote.wallMs now)
  constructor
  · simpa [hWall] using (max3_ge_mid localHlc.wallMs remote.wallMs now)
  · simpa [hWall] using (max3_ge_right localHlc.wallMs remote.wallMs now)

end CrdtBase
