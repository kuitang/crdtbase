import CrdtBase.Convergence.Defs
import CrdtBase.Crdt.Lww.Props
import CrdtBase.Crdt.MvRegister.Props
import CrdtBase.Crdt.OrSet.Props
import CrdtBase.Crdt.PnCounter.Props

set_option autoImplicit false

namespace CrdtBase

namespace Convergence

/-- Any two permutation-equivalent op streams converge for right-commutative folds. -/
theorem convergence_of_perm {σ α : Type}
    (step : σ → α → σ) [RightCommutative step]
    (init : σ) {ops₁ ops₂ : List α} (hPerm : List.Perm ops₁ ops₂) :
    applyOps step init ops₁ = applyOps step init ops₂ := by
  simpa [applyOps] using (hPerm.foldl_eq (f := step) init)

/-- Same convergence law phrased through the `SameOps` wrapper. -/
theorem convergence_of_same_ops {σ α : Type}
    (step : σ → α → σ) [RightCommutative step]
    (init : σ) {ops₁ ops₂ : List α} (hSame : SameOps ops₁ ops₂) :
    applyOps step init ops₁ = applyOps step init ops₂ := by
  exact convergence_of_perm step init hSame.perm

/-- Convergence for binary merges once global commutativity and associativity hold. -/
theorem convergence_of_comm_assoc {α : Type}
    (merge : α → α → α)
    (hComm : ∀ a b : α, merge a b = merge b a)
    (hAssoc : ∀ a b c : α, merge (merge a b) c = merge a (merge b c))
    (init : α) {ops₁ ops₂ : List α}
    (hPerm : List.Perm ops₁ ops₂) :
    applyOps merge init ops₁ = applyOps merge init ops₂ := by
  letI : RightCommutative merge := ⟨by
    intro a b c
    calc
      merge (merge a b) c = merge a (merge b c) := hAssoc a b c
      _ = merge a (merge c b) := by rw [hComm b c]
      _ = merge (merge a c) b := (hAssoc a c b).symm
    ⟩
  exact convergence_of_perm merge init hPerm

section Composite

variable {α β : Type}

/-- Componentwise merge for a 2-column composite row state. -/
def mergeComposite
    (mergeA : α → α → α)
    (mergeB : β → β → β)
    (left right : α × β) : α × β :=
  (mergeA left.1 right.1, mergeB left.2 right.2)

/-- Composite convergence for a row with two independent CRDT columns. -/
theorem convergence_composite
    (mergeA : α → α → α)
    (mergeB : β → β → β)
    (hCommA : ∀ a b : α, mergeA a b = mergeA b a)
    (hAssocA : ∀ a b c : α, mergeA (mergeA a b) c = mergeA a (mergeA b c))
    (hCommB : ∀ a b : β, mergeB a b = mergeB b a)
    (hAssocB : ∀ a b c : β, mergeB (mergeB a b) c = mergeB a (mergeB b c))
    (init : α × β) {ops₁ ops₂ : List (α × β)}
    (hPerm : List.Perm ops₁ ops₂) :
    applyOps (mergeComposite mergeA mergeB) init ops₁ =
      applyOps (mergeComposite mergeA mergeB) init ops₂ := by
  have hComm :
      ∀ a b : α × β,
        mergeComposite mergeA mergeB a b = mergeComposite mergeA mergeB b a := by
    intro a b
    cases a with
    | mk a1 a2 =>
        cases b with
        | mk b1 b2 =>
            simp [mergeComposite, hCommA a1 b1, hCommB a2 b2]
  have hAssoc :
      ∀ a b c : α × β,
        mergeComposite mergeA mergeB (mergeComposite mergeA mergeB a b) c =
          mergeComposite mergeA mergeB a (mergeComposite mergeA mergeB b c) := by
    intro a b c
    cases a with
    | mk a1 a2 =>
        cases b with
        | mk b1 b2 =>
            cases c with
            | mk c1 c2 =>
                simp [mergeComposite, hAssocA a1 b1 c1, hAssocB a2 b2 c2]
  exact convergence_of_comm_assoc (mergeComposite mergeA mergeB) hComm hAssoc init hPerm

end Composite

section Lww

variable {α : Type}

/-- LWW convergence once merge commutativity and associativity are available. -/
theorem convergence_lww
    (init : LwwRegister α) {ops₁ ops₂ : List (LwwRegister α)}
    (hPerm : List.Perm ops₁ ops₂)
    (hComm : ∀ a b : LwwRegister α, LwwRegister.merge a b = LwwRegister.merge b a)
    (hAssoc : ∀ a b c : LwwRegister α,
      LwwRegister.merge (LwwRegister.merge a b) c =
        LwwRegister.merge a (LwwRegister.merge b c)) :
    applyOps LwwRegister.merge init ops₁ = applyOps LwwRegister.merge init ops₂ := by
  exact convergence_of_comm_assoc LwwRegister.merge hComm hAssoc init hPerm

/-- LWW convergence under global event-consistency and comparator axioms. -/
theorem convergence_lww_of_consistent
    (init : LwwRegister α) {ops₁ ops₂ : List (LwwRegister α)}
    (hPerm : List.Perm ops₁ ops₂)
    (hCons : ∀ a b : LwwRegister α, LwwConsistentPair a b)
    (hSwapLt : ∀ a b : LwwRegister α,
      Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .lt →
        Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .gt)
    (hSwapGt : ∀ a b : LwwRegister α,
      Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) = .gt →
        Hlc.compareWithSite (b.hlc, b.site) (a.hlc, a.site) = .lt)
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
    applyOps LwwRegister.merge init ops₁ = applyOps LwwRegister.merge init ops₂ := by
  apply convergence_lww init hPerm
  · exact lww_merge_comm_global_of_consistent hCons hSwapLt hSwapGt hSelf
  · exact lww_merge_assoc_global_of_consistent hCons hTransLt hTransGt hSelf

end Lww

instance : Std.Commutative PnCounter.merge where
  comm := pn_counter_merge_comm

instance : Std.Associative PnCounter.merge where
  assoc := pn_counter_merge_assoc

/-- PN-counter convergence: permutation of delivered states does not change the fold result. -/
theorem convergence_pn_counter
    (init : PnCounter) {ops₁ ops₂ : List PnCounter}
    (hPerm : List.Perm ops₁ ops₂) :
    applyOps PnCounter.merge init ops₁ = applyOps PnCounter.merge init ops₂ := by
  exact convergence_of_perm PnCounter.merge init hPerm

section OrSet

variable {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]

instance : Std.Commutative (OrSet.merge (α := α) (Hlc := Hlc)) where
  comm := or_set_merge_comm

instance : Std.Associative (OrSet.merge (α := α) (Hlc := Hlc)) where
  assoc := or_set_merge_assoc

/-- OR-Set convergence: permutation of delivered states does not change the fold result. -/
theorem convergence_or_set
    (init : OrSet α Hlc) {ops₁ ops₂ : List (OrSet α Hlc)}
    (hPerm : List.Perm ops₁ ops₂) :
    applyOps (OrSet.merge (α := α) (Hlc := Hlc)) init ops₁ =
      applyOps (OrSet.merge (α := α) (Hlc := Hlc)) init ops₂ := by
  exact convergence_of_perm (OrSet.merge (α := α) (Hlc := Hlc)) init hPerm

end OrSet

section MvRegister

variable {α : Type} [DecidableEq α]

instance : Std.Commutative (MvRegister.merge (α := α)) where
  comm := mv_register_merge_comm

instance : Std.Associative (MvRegister.merge (α := α)) where
  assoc := mv_register_merge_assoc

/-- MV-register convergence: permutation of delivered states does not change the fold result. -/
theorem convergence_mv_register
    (init : MvRegister α) {ops₁ ops₂ : List (MvRegister α)}
    (hPerm : List.Perm ops₁ ops₂) :
    applyOps (MvRegister.merge (α := α)) init ops₁ =
      applyOps (MvRegister.merge (α := α)) init ops₂ := by
  exact convergence_of_perm (MvRegister.merge (α := α)) init hPerm

end MvRegister

end Convergence

end CrdtBase
