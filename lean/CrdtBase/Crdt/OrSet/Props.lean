import CrdtBase.Crdt.OrSet.Defs

set_option autoImplicit false

namespace CrdtBase

/-- OR-Set merge is commutative. -/
theorem or_set_merge_comm [DecidableEq α] [DecidableEq Hlc]
    (a b : OrSet α Hlc) : OrSet.merge a b = OrSet.merge b a := by
  ext x <;>
    simp [OrSet.merge, Finset.union_comm, Finset.union_left_comm, Finset.union_assoc]

/-- OR-Set merge is associative. -/
theorem or_set_merge_assoc [DecidableEq α] [DecidableEq Hlc]
    (a b c : OrSet α Hlc) :
    OrSet.merge (OrSet.merge a b) c = OrSet.merge a (OrSet.merge b c) := by
  ext x <;>
    simp [OrSet.merge, Finset.union_comm, Finset.union_left_comm, Finset.union_assoc]

/-- OR-Set merge is idempotent. -/
theorem or_set_merge_idem [DecidableEq α] [DecidableEq Hlc]
    (a : OrSet α Hlc) : OrSet.merge a a = a := by
  ext x <;>
    simp [OrSet.merge]

end CrdtBase
