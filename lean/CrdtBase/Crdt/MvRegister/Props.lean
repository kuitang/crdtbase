import CrdtBase.Crdt.MvRegister.Defs

set_option autoImplicit false

namespace CrdtBase

/-- MV-register merge is commutative. -/
theorem mv_register_merge_comm {α : Type} [DecidableEq α]
    (a b : MvRegister α) : MvRegister.merge a b = MvRegister.merge b a := by
  ext x
  simp [MvRegister.merge, Finset.union_comm]

/-- MV-register merge is associative. -/
theorem mv_register_merge_assoc {α : Type} [DecidableEq α]
    (a b c : MvRegister α) :
    MvRegister.merge (MvRegister.merge a b) c = MvRegister.merge a (MvRegister.merge b c) := by
  ext x
  simp [MvRegister.merge, Finset.union_assoc]

/-- MV-register merge is idempotent. -/
theorem mv_register_merge_idem {α : Type} [DecidableEq α]
    (a : MvRegister α) : MvRegister.merge a a = a := by
  ext x
  simp [MvRegister.merge]

end CrdtBase
