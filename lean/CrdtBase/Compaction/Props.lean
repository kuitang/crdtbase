import CrdtBase.Compaction.Defs

set_option autoImplicit false

namespace CrdtBase

namespace Compaction

/-- Split compaction is equivalent to a single fold over the full op sequence. -/
theorem foldPrefixSuffix_eq_foldl {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) (split : Nat) :
    foldPrefixSuffix step init ops split = List.foldl step init ops := by
  calc
    foldPrefixSuffix step init ops split
        = List.foldl step (List.foldl step init (List.take split ops)) (List.drop split ops) := by
            rfl
    _ = List.foldl step init (List.take split ops ++ List.drop split ops) := by
          simpa using
            (List.foldl_append
              (f := step)
              (b := init)
              (l := List.take split ops)
              (l' := List.drop split ops)).symm
    _ = List.foldl step init ops := by
          exact congrArg (List.foldl step init) (List.take_append_drop split ops)

/-- Same law as `foldPrefixSuffix_eq_foldl`, stated explicitly for all split points. -/
theorem foldPrefixSuffix_eq_foldl_all {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) :
    ∀ split : Nat, foldPrefixSuffix step init ops split = List.foldl step init ops := by
  intro split
  simpa using foldPrefixSuffix_eq_foldl step init ops split

/-- Canonical compaction law: compacting a prefix and folding the suffix
is equivalent to folding the full stream. -/
theorem compaction_preserves_state {α β : Type}
    (step : β → α → β) (init : β) (preOps postOps : List α) :
    List.foldl step (List.foldl step init preOps) postOps =
      List.foldl step init (preOps ++ postOps) := by
  exact
    (List.foldl_append
      (f := step)
      (b := init)
      (l := preOps)
      (l' := postOps)).symm

/-- Idempotence of compaction with no new deltas: compacting again leaves state unchanged. -/
theorem compaction_idempotent {α β : Type}
    (step : β → α → β) (init : β) (ops : List α) (split : Nat) :
    foldPrefixSuffix step (foldPrefixSuffix step init ops split) [] split =
      foldPrefixSuffix step init ops split := by
  simp [foldPrefixSuffix]

/-- PN-counter compaction preserves state for any prefix/suffix split. -/
theorem pn_counter_compaction_preserves_state
    (ops : List PnCounter) (split : Nat) :
    foldPrefixSuffix PnCounter.merge pnCounterEmpty ops split =
      List.foldl PnCounter.merge pnCounterEmpty ops := by
  simpa using
    (foldPrefixSuffix_eq_foldl
      (step := PnCounter.merge)
      (init := pnCounterEmpty)
      (ops := ops)
      (split := split))

/-- OR-Set compaction preserves state for any prefix/suffix split. -/
theorem or_set_compaction_preserves_state {α Hlc : Type}
    [DecidableEq α] [DecidableEq Hlc]
    (ops : List (OrSet α Hlc)) (split : Nat) :
    foldPrefixSuffix OrSet.merge (orSetEmpty α Hlc) ops split =
      List.foldl OrSet.merge (orSetEmpty α Hlc) ops := by
  simpa using
    (foldPrefixSuffix_eq_foldl
      (step := OrSet.merge)
      (init := orSetEmpty α Hlc)
      (ops := ops)
      (split := split))

/-- MV-register compaction preserves state for any prefix/suffix split. -/
theorem mv_register_compaction_preserves_state {α : Type}
    [DecidableEq α]
    (ops : List (MvRegister α)) (split : Nat) :
    foldPrefixSuffix MvRegister.merge (mvRegisterEmpty α) ops split =
      List.foldl MvRegister.merge (mvRegisterEmpty α) ops := by
  simpa using
    (foldPrefixSuffix_eq_foldl
      (step := MvRegister.merge)
      (init := mvRegisterEmpty α)
      (ops := ops)
      (split := split))

/-- LWW compaction (with optional empty base) preserves state for any split. -/
theorem lww_compaction_preserves_state {α : Type}
    (ops : List (LwwRegister α)) (split : Nat) :
    foldPrefixSuffix lwwStep none ops split =
      List.foldl lwwStep none ops := by
  simpa using
    (foldPrefixSuffix_eq_foldl
      (step := lwwStep)
      (init := (none : Option (LwwRegister α)))
      (ops := ops)
      (split := split))

end Compaction

end CrdtBase
