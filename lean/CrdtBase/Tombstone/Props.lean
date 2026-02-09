import CrdtBase.Tombstone.Defs

set_option autoImplicit false

namespace CrdtBase

namespace Tombstone

/-- A later delete event wins over an earlier live/write event. -/
theorem delete_wins_if_later
    (live delete : TombstoneState)
    (hLater :
      Hlc.compareWithSite (live.hlc, live.site) (delete.hlc, delete.site) = .lt) :
    merge live delete = delete := by
  unfold merge LwwRegister.merge
  simp [hLater]

/-- A later live/write event resurrects over an earlier delete event. -/
theorem write_resurrects_if_later
    (delete live : TombstoneState)
    (hLater :
      Hlc.compareWithSite (delete.hlc, delete.site) (live.hlc, live.site) = .lt) :
    merge delete live = live := by
  unfold merge LwwRegister.merge
  simp [hLater]

/-- Without new writes, tombstoned state is stable under repeated merges. -/
theorem tombstone_stable_without_new_writes
    (state : TombstoneState) :
    merge state state = state := by
  unfold merge LwwRegister.merge
  cases Hlc.compareWithSite (state.hlc, state.site) (state.hlc, state.site) <;> simp

end Tombstone

end CrdtBase
