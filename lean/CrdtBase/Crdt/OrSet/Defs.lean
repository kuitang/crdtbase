import Std.Data.Finset

set_option autoImplicit false

namespace CrdtBase

/-- A tag identifying a specific add event in an OR-Set. -/
structure OrSetTag (Hlc : Type) where
  addHlc  : Hlc
  addSite : String
  deriving Repr, DecidableEq

/-- An element in an OR-Set, tagged with its add-origin. -/
structure OrSetElem (α : Type) (Hlc : Type) where
  val : α
  tag : OrSetTag Hlc
  deriving Repr, DecidableEq

/-- An Observed-Remove Set with tombstones for removed tags. -/
structure OrSet (α : Type) (Hlc : Type) where
  elements   : Finset (OrSetElem α Hlc)
  tombstones : Finset (OrSetTag Hlc)
  deriving Repr

/-- Merge: union elements and tombstones, then filter elements by tombstones. -/
@[simp]
def OrSet.merge [DecidableEq α] [DecidableEq Hlc]
    (a b : OrSet α Hlc) : OrSet α Hlc :=
  let mergedElems := a.elements ∪ b.elements
  let mergedTombs := a.tombstones ∪ b.tombstones
  let filtered := mergedElems.filter (fun e => e.tag ∉ mergedTombs)
  { elements := filtered, tombstones := mergedTombs }

/-- Materialize: project to visible values (tags suppressed by tombstones). -/
def OrSet.values [DecidableEq α] [DecidableEq Hlc]
    (s : OrSet α Hlc) : Finset α :=
  s.elements.image (fun e => e.val)

end CrdtBase
