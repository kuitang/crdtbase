import CrdtBase.Crdt.Lww.Defs

set_option autoImplicit false

namespace CrdtBase

open Hlc
open LwwRegister

/-- Swapping arguments flips the comparison ordering. -/
theorem compareWithSite_swap (a b : Hlc × String) :
    Hlc.compareWithSite a b = Ordering.lt →
    Hlc.compareWithSite b a = Ordering.gt := by
  intro h
  unfold Hlc.compareWithSite at h ⊢
  cases hPack : compare a.1.pack b.1.pack with
  | lt =>
      have hPackSwap : compare b.1.pack a.1.pack = Ordering.gt :=
        Std.OrientedCmp.gt_of_lt (cmp := (compare : Nat → Nat → Ordering)) hPack
      simpa [hPack, hPackSwap]
  | eq =>
      have hSite : compare a.2 b.2 = Ordering.lt := by
        simpa [hPack] using h
      have hPackSwap : compare b.1.pack a.1.pack = Ordering.eq :=
        Std.OrientedCmp.eq_symm (cmp := (compare : Nat → Nat → Ordering)) hPack
      have hSiteSwap : compare b.2 a.2 = Ordering.gt :=
        Std.OrientedCmp.gt_of_lt (cmp := (compare : String → String → Ordering)) hSite
      simpa [hPackSwap, hSiteSwap]
  | gt =>
      simp [hPack] at h

/-- LWW merge is commutative. -/
theorem lww_merge_comm {α : Type} (a b : LwwRegister α) :
    LwwRegister.merge a b = LwwRegister.merge b a := by
  unfold LwwRegister.merge
  cases h : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) <;>
    simp [h, compareWithSite_swap] at *

/-- LWW merge is associative. -/
theorem lww_merge_assoc {α : Type} (a b c : LwwRegister α) :
    LwwRegister.merge (LwwRegister.merge a b) c =
      LwwRegister.merge a (LwwRegister.merge b c) := by
  unfold LwwRegister.merge
  cases hab : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) <;>
    cases hbc : Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) <;>
    cases hac : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) <;>
    simp [hab, hbc, hac, compareWithSite_swap] at *

/-- LWW merge is idempotent. -/
theorem lww_merge_idem {α : Type} (a : LwwRegister α) :
    LwwRegister.merge a a = a := by
  simp [LwwRegister.merge, Hlc.compareWithSite]

end CrdtBase
