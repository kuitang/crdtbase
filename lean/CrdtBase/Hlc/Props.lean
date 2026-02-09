import Batteries
import CrdtBase.Hlc.Defs
import Mathlib.Order.Defs.LinearOrder

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
    (_h : Hlc.recv localHlc remote now = some out)
    : out.wallMs < wallMsMax ∧ out.counter < counterMax := by
  exact ⟨out.wallMs_lt, out.counter_lt⟩

/-- Any successful now result remains within the declared bounds. -/
theorem now_some_bounds
    (localHlc : Hlc)
    (wall : Nat)
    (out : Hlc)
    (_h : Hlc.now localHlc wall = some out)
    : out.wallMs < wallMsMax ∧ out.counter < counterMax := by
  exact ⟨out.wallMs_lt, out.counter_lt⟩

/-- max3 dominates each of its arguments. -/
theorem max3_ge_left (a b c : Nat) : a ≤ Hlc.max3 a b c := by
  exact Nat.le_max_left a (max b c)

/-- max3 dominates each of its arguments (middle). -/
theorem max3_ge_mid (a b c : Nat) : b ≤ Hlc.max3 a b c := by
  exact Nat.le_trans (Nat.le_max_left b c) (Nat.le_max_right a (max b c))

/-- max3 dominates each of its arguments (right). -/
theorem max3_ge_right (a b c : Nat) : c ≤ Hlc.max3 a b c := by
  exact Nat.le_trans (Nat.le_max_right b c) (Nat.le_max_right a (max b c))

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

/-- Packed HLC values are totally ordered by `<`. -/
theorem hlc_total_order (a b : Hlc) :
    a.pack < b.pack ∨ a.pack = b.pack ∨ b.pack < a.pack := by
  exact Nat.lt_trichotomy a.pack b.pack

/-- Higher wall-clock component always yields a larger packed HLC. -/
theorem hlc_pack_preserves_order
    (a b : Hlc)
    (hWall : a.wallMs > b.wallMs) :
    a.pack > b.pack := by
  have hPackUpper : b.pack < (b.wallMs + 1) * counterMax := by
    unfold Hlc.pack
    have hAdd :
        b.wallMs * counterMax + b.counter < b.wallMs * counterMax + counterMax := by
      exact Nat.add_lt_add_left b.counter_lt (b.wallMs * counterMax)
    simpa [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] using hAdd
  have hWallSucc : b.wallMs + 1 ≤ a.wallMs := Nat.succ_le_of_lt hWall
  have hMul : (b.wallMs + 1) * counterMax ≤ a.wallMs * counterMax := by
    exact Nat.mul_le_mul_right counterMax hWallSucc
  have hLower : (b.wallMs + 1) * counterMax ≤ a.pack := by
    unfold Hlc.pack
    exact Nat.le_trans hMul (Nat.le_add_right _ _)
  exact Nat.lt_of_lt_of_le hPackUpper hLower

/-- With equal wall-clock parts, packed order is exactly counter order. -/
theorem hlc_counter_breaks_tie
    (a b : Hlc)
    (hWall : a.wallMs = b.wallMs) :
    (a.pack < b.pack ↔ a.counter < b.counter) := by
  constructor
  · intro hLt
    have hLifted :
        a.wallMs * counterMax + a.counter < a.wallMs * counterMax + b.counter := by
      simpa [Hlc.pack, hWall] using hLt
    exact Nat.lt_of_add_lt_add_left hLifted
  · intro hLt
    have hLifted :
        a.wallMs * counterMax + a.counter < a.wallMs * counterMax + b.counter := by
      exact Nat.add_lt_add_left hLt (a.wallMs * counterMax)
    simpa [Hlc.pack, hWall] using hLifted

/-- Extended `(hlc, site)` comparison is total over ordering constructors. -/
theorem hlc_site_tiebreak_total (a b : Hlc × String) :
    Hlc.compareWithSite a b = .lt ∨
      Hlc.compareWithSite a b = .eq ∨
      Hlc.compareWithSite a b = .gt := by
  cases Hlc.compareWithSite a b <;> simp

/-- Self-comparison for `(hlc, site)` is reflexive. -/
theorem compareWithSite_self_eq (a : Hlc × String) :
    Hlc.compareWithSite a a = .eq := by
  simp [Hlc.compareWithSite]

private def siteLexLt (a b : Hlc × String) : Prop :=
  a.1.pack < b.1.pack ∨ (a.1.pack = b.1.pack ∧ a.2 < b.2)

private theorem compareWithSite_eq_lt_iff (a b : Hlc × String) :
    Hlc.compareWithSite a b = .lt ↔ siteLexLt a b := by
  rcases a with ⟨ha, sa⟩
  rcases b with ⟨hb, sb⟩
  unfold Hlc.compareWithSite siteLexLt
  by_cases hPackLt : ha.pack < hb.pack
  · simp [hPackLt]
  · by_cases hPackGt : hb.pack < ha.pack
    · constructor
      · intro hCmp
        simp [hPackLt, hPackGt] at hCmp
      · intro hLt
        exfalso
        rcases hLt with hLt | ⟨hEq, _⟩
        · exact hPackLt hLt
        · have hPackGt' : hb.pack < hb.pack := by
            rw [hEq] at hPackGt
            exact hPackGt
          exact Nat.lt_irrefl hb.pack hPackGt'
    · have hPackEq : ha.pack = hb.pack := by
        exact Nat.le_antisymm (Nat.le_of_not_gt hPackGt) (Nat.le_of_not_gt hPackLt)
      constructor
      · intro hCmp
        have hSiteCmp :
            (if hSiteLt : sa < sb then Ordering.lt
              else if hSiteGt : sb < sa then Ordering.gt else Ordering.eq) = Ordering.lt := by
          simpa [hPackLt, hPackGt] using hCmp
        by_cases hSiteLt : sa < sb
        · exact Or.inr ⟨hPackEq, hSiteLt⟩
        · exfalso
          by_cases hSiteGt : sb < sa <;> simp [hSiteLt, hSiteGt] at hSiteCmp
      · intro hLt
        rcases hLt with hLt | ⟨_, hSiteLt⟩
        · exact False.elim (hPackLt hLt)
        · have hSiteGt : ¬ sb < sa := by
            intro hSiteGt
            exact String.lt_asymm hSiteLt hSiteGt
          simp [hPackLt, hPackGt, hSiteLt]

private theorem siteLexLt_trans
    {a b c : Hlc × String}
    (hab : siteLexLt a b)
    (hbc : siteLexLt b c) :
    siteLexLt a c := by
  rcases a with ⟨ha, sa⟩
  rcases b with ⟨hb, sb⟩
  rcases c with ⟨hc, sc⟩
  rcases hab with hAB | ⟨hABEq, hABSite⟩
  · rcases hbc with hBC | ⟨hBCEq, _⟩
    · exact Or.inl (Nat.lt_trans hAB hBC)
    · exact Or.inl (by simpa [hBCEq] using hAB)
  · rcases hbc with hBC | ⟨hBCEq, hBCSite⟩
    · exact Or.inl (by simpa [hABEq] using hBC)
    · have hACEq : ha.pack = hc.pack := by simpa [hABEq] using hBCEq
      have hACSite : sa < sc := String.lt_trans hABSite hBCSite
      exact Or.inr ⟨hACEq, hACSite⟩

private theorem compareWithSite_gt_of_siteLexLt
    {a b : Hlc × String}
    (h : siteLexLt a b) :
    Hlc.compareWithSite b a = .gt := by
  rcases a with ⟨ha, sa⟩
  rcases b with ⟨hb, sb⟩
  rcases h with hPackLt | ⟨hPackEq, hSiteLt⟩
  · have hPackGt : ¬ hb.pack < ha.pack := by
      intro hPackGt
      exact Nat.lt_asymm hPackLt hPackGt
    simp [Hlc.compareWithSite, hPackGt, hPackLt]
  · have hPackLtFalse : ¬ ha.pack < hb.pack := by
      intro hPackLt
      have hPackLt' : hb.pack < hb.pack := by
        rw [hPackEq] at hPackLt
        exact hPackLt
      exact Nat.lt_irrefl hb.pack hPackLt'
    have hPackGtFalse : ¬ hb.pack < ha.pack := by
      intro hPackGt
      have hPackGt' : ha.pack < ha.pack := by
        rw [← hPackEq] at hPackGt
        exact hPackGt
      exact Nat.lt_irrefl ha.pack hPackGt'
    have hSiteGtFalse : ¬ sb < sa := by
      intro hSiteGt
      exact String.lt_asymm hSiteLt hSiteGt
    simp [Hlc.compareWithSite, hPackLtFalse, hPackGtFalse, hSiteLt, hSiteGtFalse]

/-- If `(a,siteA) < (b,siteB)`, swapping arguments yields `.gt`. -/
theorem compareWithSite_swap_lt
    {a b : Hlc × String}
    (h : Hlc.compareWithSite a b = .lt) :
    Hlc.compareWithSite b a = .gt := by
  have habLt : siteLexLt a b := (compareWithSite_eq_lt_iff a b).1 h
  exact compareWithSite_gt_of_siteLexLt habLt

/-- If `(a,siteA) > (b,siteB)`, swapping arguments yields `.lt`. -/
theorem compareWithSite_swap_gt
    {a b : Hlc × String}
    (h : Hlc.compareWithSite a b = .gt) :
    Hlc.compareWithSite b a = .lt := by
  rcases a with ⟨ha, sa⟩
  rcases b with ⟨hb, sb⟩
  by_cases hPackGt : hb.pack < ha.pack
  · simp [Hlc.compareWithSite, hPackGt]
  · by_cases hPackLt : ha.pack < hb.pack
    · have hImpossible : Hlc.compareWithSite (ha, sa) (hb, sb) = .lt := by
        simp [Hlc.compareWithSite, hPackLt]
      have : False := by
        have hContr : Ordering.lt = Ordering.gt := hImpossible.symm.trans h
        cases hContr
      exact False.elim this
    · have hSiteGt : sb < sa := by
        have hSite :
            (if hSiteLt : sa < sb then Ordering.lt
              else if hSiteGt : sb < sa then Ordering.gt else Ordering.eq) = Ordering.gt := by
          simpa [Hlc.compareWithSite, hPackLt, hPackGt] using h
        by_cases hSiteGt : sb < sa
        · exact hSiteGt
        · exfalso
          by_cases hSiteLt : sa < sb <;> simp [hSiteGt, hSiteLt] at hSite
      simp [Hlc.compareWithSite, hPackGt, hPackLt, hSiteGt]

/-- Transitivity of `.lt` for `compareWithSite`. -/
theorem compareWithSite_trans_lt
    {a b c : Hlc × String}
    (hab : Hlc.compareWithSite a b = .lt)
    (hbc : Hlc.compareWithSite b c = .lt) :
    Hlc.compareWithSite a c = .lt := by
  have habLt : siteLexLt a b := (compareWithSite_eq_lt_iff a b).1 hab
  have hbcLt : siteLexLt b c := (compareWithSite_eq_lt_iff b c).1 hbc
  have hacLt : siteLexLt a c := siteLexLt_trans habLt hbcLt
  exact (compareWithSite_eq_lt_iff a c).2 hacLt

/-- Transitivity of `.gt` for `compareWithSite`. -/
theorem compareWithSite_trans_gt
    {a b c : Hlc × String}
    (hab : Hlc.compareWithSite a b = .gt)
    (hbc : Hlc.compareWithSite b c = .gt) :
    Hlc.compareWithSite a c = .gt := by
  have hba : Hlc.compareWithSite b a = .lt := compareWithSite_swap_gt hab
  have hcb : Hlc.compareWithSite c b = .lt := compareWithSite_swap_gt hbc
  have hca : Hlc.compareWithSite c a = .lt := compareWithSite_trans_lt hcb hba
  exact compareWithSite_swap_lt hca

/-- If two HLCs share the same wall-clock component, packed order matches counter order. -/
theorem pack_lt_of_same_wall_counter_lt
    (a b : Hlc)
    (hWall : a.wallMs = b.wallMs)
    (hCounter : a.counter < b.counter) :
    a.pack < b.pack := by
  have hLifted :
      a.wallMs * counterMax + a.counter < a.wallMs * counterMax + b.counter := by
    exact Nat.add_lt_add_left hCounter (a.wallMs * counterMax)
  simpa [Hlc.pack, hWall] using hLifted

/-- Successful `now` strictly increases packed HLC order. -/
theorem hlc_now_monotonic
    (localHlc : Hlc)
    (wall : Nat)
    (out : Hlc)
    (h : Hlc.now localHlc wall = some out)
    : localHlc.pack < out.pack := by
  have hNow :
      ∃ hWall hCounter,
        { wallMs := max localHlc.wallMs wall
          , counter :=
              if max localHlc.wallMs wall = localHlc.wallMs then
                localHlc.counter + 1
              else
                0
          , wallMs_lt := hWall
          , counter_lt := hCounter
          } = out := by
    simpa [Hlc.now, Hlc.mk?] using h
  rcases hNow with ⟨_, _, hEq⟩
  have hOutWallRaw : max localHlc.wallMs wall = out.wallMs := by
    simpa using congrArg Hlc.wallMs hEq
  have hOutWall : out.wallMs = max localHlc.wallMs wall := hOutWallRaw.symm
  have hOutCounterRaw :
      (if max localHlc.wallMs wall = localHlc.wallMs then localHlc.counter + 1 else 0) =
        out.counter := by
    simpa using congrArg Hlc.counter hEq
  have hOutCounter :
      out.counter =
        (if max localHlc.wallMs wall = localHlc.wallMs then localHlc.counter + 1 else 0) :=
    hOutCounterRaw.symm
  by_cases hWallEq : max localHlc.wallMs wall = localHlc.wallMs
  · have hCounterEq : out.counter = localHlc.counter + 1 := by
      simpa [hWallEq] using hOutCounter
    have hOutWallEq : out.wallMs = localHlc.wallMs := by
      simpa [hWallEq] using hOutWall
    have hCounterLt : localHlc.counter < out.counter := by
      simp [hCounterEq]
    have hOutPackLt : localHlc.pack < out.pack := by
      exact pack_lt_of_same_wall_counter_lt localHlc out hOutWallEq.symm hCounterLt
    exact hOutPackLt
  · have hLocalNeMax : localHlc.wallMs ≠ max localHlc.wallMs wall := by
      intro hEqWall
      exact hWallEq hEqWall.symm
    have hWallLt : localHlc.wallMs < max localHlc.wallMs wall := by
      exact Nat.lt_of_le_of_ne (Nat.le_max_left localHlc.wallMs wall) hLocalNeMax
    have hOutWallGt : out.wallMs > localHlc.wallMs := by
      simpa [hOutWall] using hWallLt
    exact hlc_pack_preserves_order out localHlc hOutWallGt

/-- Alias of `hlc_now_monotonic` using the strict-monotonic naming from the spec. -/
theorem hlc_now_strict_monotonic
    (localHlc : Hlc)
    (wall : Nat)
    (out : Hlc)
    (h : Hlc.now localHlc wall = some out)
    : localHlc.pack < out.pack := by
  exact hlc_now_monotonic localHlc wall out h

/-- Successful `recv` strictly increases packed HLC order over both local and remote inputs. -/
theorem hlc_recv_monotonic
    (localHlc remote : Hlc)
    (now : Nat)
    (out : Hlc)
    (h : Hlc.recv localHlc remote now = some out)
    : localHlc.pack < out.pack ∧ remote.pack < out.pack := by
  have hWalls := recv_wallMs_monotonic localHlc remote now out h
  rcases hWalls with ⟨hLocalWallLe, hRemoteWallLe, _⟩
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
  have hCounterRaw : Hlc.recvCounter localHlc remote now = out.counter := by
    simpa [Hlc.recvCounter, Hlc.recvWall] using congrArg Hlc.counter hEq
  have hCounter : out.counter = Hlc.recvCounter localHlc remote now := hCounterRaw.symm
  have hLocalPackLt : localHlc.pack < out.pack := by
    by_cases hLocalWallEq : out.wallMs = localHlc.wallMs
    · have hRecvWallLocal : Hlc.recvWall localHlc remote now = localHlc.wallMs := by
        calc
          Hlc.recvWall localHlc remote now = out.wallMs := hWall.symm
          _ = localHlc.wallMs := hLocalWallEq
      have hCounterGtLocal : localHlc.counter < Hlc.recvCounter localHlc remote now := by
        by_cases hRecvWallRemote : Hlc.recvWall localHlc remote now = remote.wallMs
        · have hCounterEq :
            Hlc.recvCounter localHlc remote now = max localHlc.counter remote.counter + 1 := by
            have hLocalEqRemote : localHlc.wallMs = remote.wallMs := by
              calc
                localHlc.wallMs = Hlc.recvWall localHlc remote now := hRecvWallLocal.symm
                _ = remote.wallMs := hRecvWallRemote
            simp [Hlc.recvCounter, hRecvWallLocal, hLocalEqRemote]
          have hCounterLt : localHlc.counter < max localHlc.counter remote.counter + 1 := by
            exact Nat.lt_succ_of_le (Nat.le_max_left localHlc.counter remote.counter)
          simpa [hCounterEq] using hCounterLt
        · have hCounterEq :
            Hlc.recvCounter localHlc remote now = localHlc.counter + 1 := by
            have hLocalNeRemote : localHlc.wallMs ≠ remote.wallMs := by
              intro hEqLocalRemote
              apply hRecvWallRemote
              calc
                Hlc.recvWall localHlc remote now = localHlc.wallMs := hRecvWallLocal
                _ = remote.wallMs := hEqLocalRemote
            simp [Hlc.recvCounter, hRecvWallLocal, hLocalNeRemote]
          simp [hCounterEq]
      have hCounterOut : localHlc.counter < out.counter := by
        simpa [hCounter] using hCounterGtLocal
      exact pack_lt_of_same_wall_counter_lt localHlc out hLocalWallEq.symm hCounterOut
    · have hLocalNeOut : localHlc.wallMs ≠ out.wallMs := by
        intro hEqLocal
        exact hLocalWallEq hEqLocal.symm
      have hLocalWallLt : localHlc.wallMs < out.wallMs := by
        exact Nat.lt_of_le_of_ne hLocalWallLe hLocalNeOut
      exact hlc_pack_preserves_order out localHlc hLocalWallLt
  have hRemotePackLt : remote.pack < out.pack := by
    by_cases hRemoteWallEq : out.wallMs = remote.wallMs
    · have hRecvWallRemote : Hlc.recvWall localHlc remote now = remote.wallMs := by
        calc
          Hlc.recvWall localHlc remote now = out.wallMs := hWall.symm
          _ = remote.wallMs := hRemoteWallEq
      have hCounterGtRemote : remote.counter < Hlc.recvCounter localHlc remote now := by
        by_cases hRecvWallLocal : Hlc.recvWall localHlc remote now = localHlc.wallMs
        · have hCounterEq :
            Hlc.recvCounter localHlc remote now = max localHlc.counter remote.counter + 1 := by
            have hLocalEqRemote : localHlc.wallMs = remote.wallMs := by
              calc
                localHlc.wallMs = Hlc.recvWall localHlc remote now := hRecvWallLocal.symm
                _ = remote.wallMs := hRecvWallRemote
            simp [Hlc.recvCounter, hRecvWallLocal, hLocalEqRemote]
          have hCounterLt : remote.counter < max localHlc.counter remote.counter + 1 := by
            exact Nat.lt_succ_of_le (Nat.le_max_right localHlc.counter remote.counter)
          simpa [hCounterEq] using hCounterLt
        · have hCounterEq :
            Hlc.recvCounter localHlc remote now = remote.counter + 1 := by
            have hRemoteNeLocal : remote.wallMs ≠ localHlc.wallMs := by
              intro hEqRemoteLocal
              apply hRecvWallLocal
              calc
                Hlc.recvWall localHlc remote now = remote.wallMs := hRecvWallRemote
                _ = localHlc.wallMs := hEqRemoteLocal
            simp [Hlc.recvCounter, hRecvWallRemote, hRemoteNeLocal]
          simp [hCounterEq]
      have hCounterOut : remote.counter < out.counter := by
        simpa [hCounter] using hCounterGtRemote
      exact pack_lt_of_same_wall_counter_lt remote out hRemoteWallEq.symm hCounterOut
    · have hRemoteNeOut : remote.wallMs ≠ out.wallMs := by
        intro hEqRemote
        exact hRemoteWallEq hEqRemote.symm
      have hRemoteWallLt : remote.wallMs < out.wallMs := by
        exact Nat.lt_of_le_of_ne hRemoteWallLe hRemoteNeOut
      exact hlc_pack_preserves_order out remote hRemoteWallLt
  exact ⟨hLocalPackLt, hRemotePackLt⟩

/-- Alias of `hlc_recv_monotonic` using the strict-monotonic naming from the spec. -/
theorem hlc_recv_strict_monotonic
    (localHlc remote : Hlc)
    (now : Nat)
    (out : Hlc)
    (h : Hlc.recv localHlc remote now = some out)
    : localHlc.pack < out.pack ∧ remote.pack < out.pack := by
  exact hlc_recv_monotonic localHlc remote now out h

end CrdtBase
