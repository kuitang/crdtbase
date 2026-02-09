import CrdtBase.Replication.Defs

set_option autoImplicit false

namespace CrdtBase

namespace Replication

theorem mem_takeContiguousFrom_mem
    (expected seq : Nat) (seqs : List Nat) :
    seq ∈ takeContiguousFrom expected seqs → seq ∈ seqs := by
  induction seqs generalizing expected with
  | nil =>
      intro h
      simp [takeContiguousFrom] at h
  | cons head tail ih =>
      intro h
      by_cases hEq : head = expected
      · simp [takeContiguousFrom, hEq] at h
        rcases h with hHead | hTail
        · have hSeqHead : seq = head := Eq.trans hHead hEq.symm
          exact List.mem_cons.mpr (Or.inl hSeqHead)
        · exact List.mem_cons.mpr (Or.inr (ih (expected := expected + 1) hTail))
      · simp [takeContiguousFrom, hEq] at h

theorem readSince_mem_gt_since
    (entries : List LogEntry) (siteId : String) (since seq : Nat)
    (hMem : seq ∈ readSince entries siteId since) :
    seq > since := by
  unfold readSince at hMem
  have hInFilter : seq ∈ (canonicalSeqs entries siteId).filter (fun candidate => candidate > since) :=
    mem_takeContiguousFrom_mem
      (expected := since + 1)
      (seq := seq)
      (seqs := (canonicalSeqs entries siteId).filter (fun candidate => candidate > since))
      hMem
  have hTrue : decide (seq > since) = true := (List.mem_filter.mp hInFilter).2
  by_cases hGt : seq > since
  · exact hGt
  · have hFalse : decide (seq > since) = false := by simp [hGt]
    rw [hFalse] at hTrue
    contradiction

end Replication

end CrdtBase
