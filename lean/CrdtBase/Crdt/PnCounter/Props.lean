import CrdtBase.Crdt.PnCounter.Defs

set_option autoImplicit false

namespace CrdtBase

/-- PN-counter merge is commutative. -/
theorem pn_counter_merge_comm (a b : PnCounter) :
    PnCounter.merge a b = PnCounter.merge b a := by
  ext site <;> simp [PnCounter.merge, Nat.max_comm]

/-- PN-counter merge is associative. -/
theorem pn_counter_merge_assoc (a b c : PnCounter) :
    PnCounter.merge (PnCounter.merge a b) c = PnCounter.merge a (PnCounter.merge b c) := by
  ext site <;> simp [PnCounter.merge, Nat.max_assoc]

/-- PN-counter merge is idempotent. -/
theorem pn_counter_merge_idem (a : PnCounter) :
    PnCounter.merge a a = a := by
  ext site <;> simp [PnCounter.merge]

end CrdtBase
