import Mathlib.Data.Finset.Image

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

@[ext] theorem OrSet.ext {α Hlc : Type} {a b : OrSet α Hlc}
    (hElements : a.elements = b.elements)
    (hTombstones : a.tombstones = b.tombstones) : a = b := by
  cases a
  cases b
  cases hElements
  cases hTombstones
  rfl

/-- Canonicalize by dropping all tombstoned add-tags from elements. -/
@[simp]
def OrSet.canonicalize {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (s : OrSet α Hlc) : OrSet α Hlc :=
  { elements := s.elements.filter (fun e => e.tag ∉ s.tombstones)
    tombstones := s.tombstones }

/-- Merge: union elements and tombstones, then filter elements by tombstones. -/
@[simp]
def OrSet.merge {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (a b : OrSet α Hlc) : OrSet α Hlc :=
  OrSet.canonicalize {
    elements := a.elements ∪ b.elements
    tombstones := a.tombstones ∪ b.tombstones
  }

/-- Materialize: project to visible values (tags suppressed by tombstones). -/
def OrSet.values {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (s : OrSet α Hlc) : Finset α :=
  Finset.image (fun e => e.val) s.elements

/-- Visible values after enforcing tombstone suppression. -/
def OrSet.visibleValues {α Hlc : Type} [DecidableEq α] [DecidableEq Hlc]
    (s : OrSet α Hlc) : Finset α :=
  Finset.image (fun e => e.val) (OrSet.canonicalize s).elements

end CrdtBase
