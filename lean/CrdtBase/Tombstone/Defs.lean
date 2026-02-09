import CrdtBase.Crdt.Lww.Defs

set_option autoImplicit false

namespace CrdtBase

namespace Tombstone

/-- Tombstone state is modeled as an LWW register over a boolean marker. -/
abbrev TombstoneState := LwwRegister Bool

/-- Construct a delete marker (`true`) event. -/
def deleteState (hlc : Hlc) (site : String) : TombstoneState :=
  { val := true
    hlc := hlc
    site := site }

/-- Construct a live/write marker (`false`) event. -/
def liveState (hlc : Hlc) (site : String) : TombstoneState :=
  { val := false
    hlc := hlc
    site := site }

/-- Tombstone merge inherits LWW ordering semantics. -/
abbrev merge : TombstoneState → TombstoneState → TombstoneState := LwwRegister.merge

/-- Materialized deletion bit. -/
def isDeleted (state : TombstoneState) : Bool :=
  state.val

end Tombstone

end CrdtBase
