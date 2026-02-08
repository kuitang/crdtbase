import CrdtBase.Crdt.Lww.Defs

set_option autoImplicit false

namespace CrdtBase

open LwwRegister

/-- Consistency for an LWW pair: equal `(hlc, site)` implies identical state. -/
def LwwConsistentPair {α : Type} (a b : LwwRegister α) : Prop :=
  Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = Ordering.eq → a = b

/-- LWW merge is commutative under event-consistency and comparator orientation assumptions. -/
theorem lww_merge_comm_of_consistent {α : Type} (a b : LwwRegister α)
    (hCons : LwwConsistentPair a b)
    (hSwapLt : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .lt →
      Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .gt)
    (hSwapGt : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .gt →
      Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .lt)
    (hSelf : ∀ x : LwwRegister α,
      Hlc.compareWithSite (x.hlc, x.site) (x.hlc, x.site) = .eq)
    : LwwRegister.merge a b = LwwRegister.merge b a := by
  unfold LwwRegister.merge
  cases hab : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) with
  | lt =>
      have hba : Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .gt := hSwapLt hab
      simp [hba]
  | eq =>
      have hEq : a = b := hCons hab
      subst hEq
      simp [hSelf]
  | gt =>
      have hba : Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .lt := hSwapGt hab
      simp [hba]

/-- LWW merge is associative under pairwise consistency and comparator transitivity assumptions. -/
theorem lww_merge_assoc_of_consistent {α : Type} (a b c : LwwRegister α)
    (hAB : LwwConsistentPair a b)
    (hBC : LwwConsistentPair b c)
    (hAC : LwwConsistentPair a c)
    (hTransLt :
      Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .lt →
      Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) = .lt →
      Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .lt)
    (hTransGt :
      Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .gt →
      Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) = .gt →
      Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .gt)
    (hSelf : ∀ x : LwwRegister α,
      Hlc.compareWithSite (x.hlc, x.site) (x.hlc, x.site) = .eq)
    : LwwRegister.merge (LwwRegister.merge a b) c =
      LwwRegister.merge a (LwwRegister.merge b c) := by
  unfold LwwRegister.merge
  cases hab : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) <;>
    cases hbc : Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) <;>
    cases hac : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) <;>
    simp [hab, hbc, hac]
  · have hacLt : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .lt := hTransLt hab hbc
    simp [hac] at hacLt
  · have hacLt : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .lt := hTransLt hab hbc
    simp [hac] at hacLt
  · have habEq : a = b := hAB hab
    have hbcEq : b = c := hBC hbc
    subst habEq
    subst hbcEq
    have hacEq : Hlc.compareWithSite (a.hlc, a.site) (a.hlc, a.site) = .eq := hSelf a
    simp [hac] at hacEq
  · have habEq : a = b := hAB hab
    subst habEq
    simp [hac] at hbc
  · have hbcEq : b = c := hBC hbc
    subst hbcEq
    simp [hac] at hab
  · have hacGt : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .gt := hTransGt hab hbc
    simp [hac] at hacGt

/-- LWW merge is idempotent when self-comparison is reflexive. -/
theorem lww_merge_idem {α : Type} (a : LwwRegister α)
    (hSelf : Hlc.compareWithSite (a.hlc, a.site) (a.hlc, a.site) = .eq)
    : LwwRegister.merge a a = a := by
  unfold LwwRegister.merge
  simp [hSelf]

end CrdtBase
