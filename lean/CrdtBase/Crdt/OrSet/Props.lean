import CrdtBase.Crdt.OrSet.Defs
import Mathlib.Tactic

set_option autoImplicit false

namespace CrdtBase

/-- Canonicalization is idempotent. -/
theorem or_set_canonicalize_idem {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (a : OrSet α Hlc) :
    OrSet.canonicalize (OrSet.canonicalize a) = OrSet.canonicalize a := by
  ext x
  · simp [OrSet.canonicalize]
  · simp [OrSet.canonicalize]

/-- Canonicalization removes all elements whose tags are tombstoned. -/
theorem or_set_canonicalize_no_tombstoned_tags {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (a : OrSet α Hlc) :
    ∀ x, x ∈ (OrSet.canonicalize a).elements → x.tag ∉ (OrSet.canonicalize a).tombstones := by
  intro x hx
  exact (Finset.mem_filter.mp hx).2

/-- Canonicalization preserves visible (non-tombstoned) value semantics. -/
theorem or_set_canonicalize_preserves_visible_values {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (a : OrSet α Hlc) :
    OrSet.visibleValues (OrSet.canonicalize a) = OrSet.visibleValues a := by
  ext x
  simp [OrSet.visibleValues, OrSet.canonicalize, and_assoc]

/-- OR-Set merge is commutative. -/
theorem or_set_merge_comm {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (a b : OrSet α Hlc) : OrSet.merge a b = OrSet.merge b a := by
  ext x <;>
    simp [OrSet.merge, Finset.union_comm]

/-- OR-Set merge is associative. -/
theorem or_set_merge_assoc {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (a b c : OrSet α Hlc) :
    OrSet.merge (OrSet.merge a b) c = OrSet.merge a (OrSet.merge b c) := by
  ext x
  · constructor <;> intro hx
    · simp [OrSet.merge, Finset.union_comm, Finset.union_left_comm] at hx ⊢
      aesop
    · simp [OrSet.merge, Finset.union_comm, Finset.union_left_comm] at hx ⊢
      aesop
  · simp [OrSet.merge, Finset.union_comm, Finset.union_left_comm]

/-- OR-Set merge is idempotent. -/
theorem or_set_merge_idem {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (a : OrSet α Hlc)
    (hClean : ∀ x ∈ a.elements, x.tag ∉ a.tombstones) :
    OrSet.merge a a = a := by
  ext x
  · constructor
    · intro hx
      simp [OrSet.merge] at hx
      exact hx.1
    · intro hx
      have hNotInTombs : x.tag ∉ a.tombstones := hClean x hx
      simp [OrSet.merge, hx, hNotInTombs]
  · simp [OrSet.merge]

end CrdtBase
