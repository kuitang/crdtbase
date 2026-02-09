import CrdtBase.Crdt.Lww.Defs
import CrdtBase.Hlc.Props

set_option autoImplicit false

namespace CrdtBase

open LwwRegister

/-- Consistency for an LWW pair: equal `(hlc, site)` implies identical state. -/
def LwwConsistentPair {α : Type} (a b : LwwRegister α) : Prop :=
  Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = Ordering.eq → a = b

/-- Under event-consistency, equal `(hlc, site)` implies equal payloads. -/
theorem lww_equal_key_implies_equal_payload {α : Type} (a b : LwwRegister α)
    (hCons : LwwConsistentPair a b)
    (hEq : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .eq) :
    a.val = b.val := by
  simp [hCons hEq]

/-- Conflicting payloads on the same `(hlc, site)` violate LWW event-consistency. -/
theorem dedup_rejects_conflicting_same_key {α : Type} (a b : LwwRegister α)
    (hEq : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .eq)
    (hValNe : a.val ≠ b.val) :
    ¬ LwwConsistentPair a b := by
  intro hCons
  exact hValNe (by simp [hCons hEq])

/-- LWW merge is commutative under event-consistency. -/
theorem lww_merge_comm_of_consistent {α : Type} (a b : LwwRegister α)
    (hCons : LwwConsistentPair a b)
    : LwwRegister.merge a b = LwwRegister.merge b a := by
  unfold LwwRegister.merge
  cases hab : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) with
  | lt =>
      have hba : Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .gt :=
        compareWithSite_swap_lt hab
      simp [hba]
  | eq =>
      have hEq : a = b := hCons hab
      subst hEq
      have hSelf : Hlc.compareWithSite (a.hlc, a.site) (a.hlc, a.site) = .eq :=
        compareWithSite_self_eq (a.hlc, a.site)
      simp [hSelf]
  | gt =>
      have hba : Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .lt :=
        compareWithSite_swap_gt hab
      simp [hba]

/-- LWW merge is associative under pairwise event-consistency. -/
theorem lww_merge_assoc_of_consistent {α : Type} (a b c : LwwRegister α)
    (hAB : LwwConsistentPair a b)
    (hBC : LwwConsistentPair b c)
    : LwwRegister.merge (LwwRegister.merge a b) c =
      LwwRegister.merge a (LwwRegister.merge b c) := by
  unfold LwwRegister.merge
  cases hab : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) <;>
    cases hbc : Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) <;>
    cases hac : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) <;>
    simp [hab, hbc, hac]
  · have hacLt : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .lt :=
      compareWithSite_trans_lt hab hbc
    simp [hac] at hacLt
  · have hacLt : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .lt :=
      compareWithSite_trans_lt hab hbc
    simp [hac] at hacLt
  · have habEq : a = b := hAB hab
    have hbcEq : b = c := hBC hbc
    subst habEq
    subst hbcEq
    have hacEq : Hlc.compareWithSite (a.hlc, a.site) (a.hlc, a.site) = .eq :=
      compareWithSite_self_eq (a.hlc, a.site)
    simp [hac] at hacEq
  · have habEq : a = b := hAB hab
    subst habEq
    simp [hac] at hbc
  · have hbcEq : b = c := hBC hbc
    subst hbcEq
    simp [hac] at hab
  · have hacGt : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .gt :=
      compareWithSite_trans_gt hab hbc
    simp [hac] at hacGt

/-- LWW merge is idempotent. -/
theorem lww_merge_idem {α : Type} (a : LwwRegister α) : LwwRegister.merge a a = a := by
  have hSelf : Hlc.compareWithSite (a.hlc, a.site) (a.hlc, a.site) = .eq :=
    compareWithSite_self_eq (a.hlc, a.site)
  unfold LwwRegister.merge
  simp [hSelf]

/-- Globalized commutativity under pairwise event-consistency. -/
theorem lww_merge_comm_global_of_consistent {α : Type}
    (hCons : ∀ a b : LwwRegister α, LwwConsistentPair a b) :
    ∀ a b : LwwRegister α, LwwRegister.merge a b = LwwRegister.merge b a := by
  intro a b
  simpa using lww_merge_comm_of_consistent a b (hCons a b)

/-- Globalized associativity under pairwise event-consistency. -/
theorem lww_merge_assoc_global_of_consistent {α : Type}
    (hCons : ∀ a b : LwwRegister α, LwwConsistentPair a b) :
    ∀ a b c : LwwRegister α,
      LwwRegister.merge (LwwRegister.merge a b) c =
        LwwRegister.merge a (LwwRegister.merge b c) := by
  intro a b c
  simpa using lww_merge_assoc_of_consistent a b c
    (hCons a b) (hCons b c)

end CrdtBase
