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
  cases hcmp : compare a.1 b.1 <;> simp [Hlc.compareWithSite] at h ⊢

/-- LWW merge is commutative. -/
theorem lww_merge_comm (a b : LwwRegister α) :
    LwwRegister.merge a b = LwwRegister.merge b a := by
  unfold LwwRegister.merge
  cases h : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) <;>
    simp [h, compareWithSite_swap] at *

/-- LWW merge is associative. -/
theorem lww_merge_assoc (a b c : LwwRegister α) :
    LwwRegister.merge (LwwRegister.merge a b) c =
      LwwRegister.merge a (LwwRegister.merge b c) := by
  unfold LwwRegister.merge
  cases hab : Hlc.compareWithSite (a.hlc, a.site) (b.hlc, b.site) <;>
    cases hbc : Hlc.compareWithSite (b.hlc, b.site) (c.hlc, c.site) <;>
    cases hac : Hlc.compareWithSite (a.hlc, a.site) (c.hlc, c.site) <;>
    simp [hab, hbc, hac, compareWithSite_swap] at *

/-- LWW merge is idempotent. -/
theorem lww_merge_idem (a : LwwRegister α) :
    LwwRegister.merge a a = a := by
  simp [LwwRegister.merge, Hlc.compareWithSite]

end CrdtBase
