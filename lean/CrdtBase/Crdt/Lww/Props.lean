import CrdtBase.Crdt.Lww.Defs

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
  have hStateEq : a = b := hCons hEq
  simpa [hStateEq]

/-- Conflicting payloads on the same `(hlc, site)` violate LWW event-consistency. -/
theorem dedup_rejects_conflicting_same_key {α : Type} (a b : LwwRegister α)
    (hEq : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .eq)
    (hValNe : a.val ≠ b.val) :
    ¬ LwwConsistentPair a b := by
  intro hCons
  have hStateEq : a = b := hCons hEq
  apply hValNe
  simpa [hStateEq]

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

/-- Globalized commutativity: if pairwise consistency and comparator swap laws hold for all pairs,
LWW merge is commutative for all values. -/
theorem lww_merge_comm_global_of_consistent {α : Type}
    (hCons : ∀ a b : LwwRegister α, LwwConsistentPair a b)
    (hSwapLt : ∀ a b : LwwRegister α,
      Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .lt →
        Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .gt)
    (hSwapGt : ∀ a b : LwwRegister α,
      Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .gt →
        Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .lt)
    (hSelf : ∀ x : LwwRegister α,
      Hlc.compareWithSite (x.hlc, x.site) (x.hlc, x.site) = .eq) :
    ∀ a b : LwwRegister α, LwwRegister.merge a b = LwwRegister.merge b a := by
  intro a b
  exact lww_merge_comm_of_consistent a b (hCons a b) (hSwapLt a b) (hSwapGt a b) hSelf

/-- Globalized associativity under global consistency and comparator transitivity assumptions. -/
theorem lww_merge_assoc_global_of_consistent {α : Type}
    (hCons : ∀ a b : LwwRegister α, LwwConsistentPair a b)
    (hTransLt : ∀ a b c : LwwRegister α,
      Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .lt →
        Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) = .lt →
        Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .lt)
    (hTransGt : ∀ a b c : LwwRegister α,
      Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .gt →
        Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) = .gt →
        Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) = .gt)
    (hSelf : ∀ x : LwwRegister α,
      Hlc.compareWithSite (x.hlc, x.site) (x.hlc, x.site) = .eq) :
    ∀ a b c : LwwRegister α,
      LwwRegister.merge (LwwRegister.merge a b) c =
        LwwRegister.merge a (LwwRegister.merge b c) := by
  intro a b c
  exact lww_merge_assoc_of_consistent a b c
    (hCons a b) (hCons b c) (hCons a c)
    (hTransLt a b c) (hTransGt a b c) hSelf

end CrdtBase
