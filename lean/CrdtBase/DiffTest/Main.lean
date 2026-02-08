import Lean
import CrdtBase.Hlc.Defs
import CrdtBase.Crdt.Lww.Defs
import CrdtBase.Crdt.PnCounter.Defs
import CrdtBase.Sql.Defs

set_option autoImplicit false

open Lean
open CrdtBase

structure HlcJson where
  wallMs : Nat
  counter : Nat
  deriving FromJson, ToJson, DecidableEq

structure LwwJson where
  val : Json
  hlc : HlcJson
  site : String
  deriving FromJson, ToJson

structure PnEntryJson where
  site : String
  n : Nat
  deriving FromJson, ToJson

structure PnJson where
  inc : List PnEntryJson
  dec : List PnEntryJson
  deriving FromJson, ToJson

structure OrSetTagJson where
  addHlc : HlcJson
  addSite : String
  deriving FromJson, ToJson

structure OrSetElemJson where
  val : Json
  tag : OrSetTagJson
  deriving FromJson, ToJson

structure OrSetJson where
  elements : List OrSetElemJson
  tombstones : List OrSetTagJson
  deriving FromJson, ToJson

structure MvValueJson where
  val : Json
  hlc : HlcJson
  site : String
  deriving FromJson, ToJson

structure MvJson where
  values : List MvValueJson
  deriving FromJson, ToJson

structure MergeCmd where
  type : String
  a : Json
  b : Json
  deriving FromJson

structure SqlGenerateOpsCmd where
  type : String
  statement : SqlWriteStatement
  context : SqlGenerationContext
  deriving FromJson

structure SqlBuildSelectPlanCmd where
  type : String
  statement : SelectStatement
  schema : SelectPlannerSchema
  deriving FromJson

def resultLine (result : Json) : String :=
  (Json.mkObj [("result", result)]).compress

def toHlc (h : HlcJson) : Except String Hlc := do
  match Hlc.mk? h.wallMs h.counter with
  | some hlc => pure hlc
  | none => throw s!"invalid HLC bounds: {h.wallMs} {h.counter}"

def fromHlc (h : Hlc) : HlcJson :=
  { wallMs := h.wallMs, counter := h.counter }

def stringLe (a b : String) : Bool :=
  match compare a b with
  | .gt => false
  | _ => true

def insertByKey {α : Type} (key : α → String) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
      if stringLe (key x) (key y) then
        x :: y :: ys
      else
        y :: insertByKey key x ys

def sortByKey {α : Type} (key : α → String) : List α → List α
  | [] => []
  | x :: xs => insertByKey key x (sortByKey key xs)

def dedupeByKey {α : Type} (key : α → String) (items : List α) : List α :=
  let rec loop (seen : List String) (acc : List α) (rest : List α) : List α :=
    match rest with
    | [] => acc.reverse
    | item :: tail =>
        let itemKey := key item
        if seen.contains itemKey then
          loop seen acc tail
        else
          loop (itemKey :: seen) (item :: acc) tail
  loop [] [] items

def checkConsistentPairs (pairs : List (String × String)) (errPrefix : String) : Except String Unit := do
  let rec loop (seen : List (String × String)) (rest : List (String × String)) : Except String Unit := do
    match rest with
    | [] => pure ()
    | (key, fp) :: tail =>
        match seen.find? (fun item => item.1 = key) with
        | none => loop ((key, fp) :: seen) tail
        | some item =>
            if item.2 = fp then
              loop seen tail
            else
              throw s!"{errPrefix}: {key}"
  loop [] pairs

def hlcEventKey (h : HlcJson) (site : String) : String :=
  s!"{h.wallMs}:{h.counter}:{site}"

def assertLwwConsistent (a b : LwwJson) : Except String Unit := do
  if (a.hlc == b.hlc) && (a.site == b.site) && a.val != b.val then
    throw "conflicting LWW event identity: same (hlc, site) with different payloads"

def toLww (input : LwwJson) : Except String (LwwRegister Json) := do
  let hlc ← toHlc input.hlc
  pure { val := input.val, hlc := hlc, site := input.site }

def fromLww (lww : LwwRegister Json) : LwwJson :=
  { val := lww.val, hlc := fromHlc lww.hlc, site := lww.site }

def handleLwwMerge (aJson bJson : Json) : Except String String := do
  let a : LwwJson ← fromJson? aJson
  let b : LwwJson ← fromJson? bJson
  assertLwwConsistent a b
  let lwwA ← toLww a
  let lwwB ← toLww b
  let merged := LwwRegister.merge lwwA lwwB
  pure (resultLine (toJson (fromLww merged)))

def lookupPnCount (entries : List PnEntryJson) (site : String) : Nat :=
  entries.foldl
    (fun acc entry => if entry.site = site then acc + entry.n else acc)
    0

def toPnCounter (input : PnJson) : PnCounter :=
  { inc := fun site => lookupPnCount input.inc site
    dec := fun site => lookupPnCount input.dec site }

def serializePnEntries (counts : String → Nat) (sites : List String) : List PnEntryJson :=
  let deduped := dedupeByKey (fun site => site) sites
  let ordered := sortByKey (fun site => site) deduped
  ordered.filterMap (fun site =>
    let n := counts site
    if n = 0 then none else some { site := site, n := n })

def fromPnCounter (counter : PnCounter) (incSites decSites : List String) : PnJson :=
  { inc := serializePnEntries counter.inc incSites
    dec := serializePnEntries counter.dec decSites }

def handlePnMerge (aJson bJson : Json) : Except String String := do
  let a : PnJson ← fromJson? aJson
  let b : PnJson ← fromJson? bJson
  let pnA := toPnCounter a
  let pnB := toPnCounter b
  let merged := PnCounter.merge pnA pnB
  let out := fromPnCounter merged
    (a.inc.map (·.site) ++ b.inc.map (·.site))
    (a.dec.map (·.site) ++ b.dec.map (·.site))
  pure (resultLine (toJson out))

def orSetTagKey (tag : OrSetTagJson) : String :=
  hlcEventKey tag.addHlc tag.addSite

def orSetElemEventKey (elem : OrSetElemJson) : String :=
  orSetTagKey elem.tag

def orSetElemSortKey (elem : OrSetElemJson) : String :=
  s!"{orSetTagKey elem.tag}:{(toJson elem.val).compress}"

def validateOrSetHlcBounds (input : OrSetJson) : Except String Unit := do
  for tag in input.tombstones do
    let _ ← toHlc tag.addHlc
    pure ()
  for elem in input.elements do
    let _ ← toHlc elem.tag.addHlc
    pure ()

def assertOrSetConsistent (elements : List OrSetElemJson) : Except String Unit := do
  let pairs := elements.map (fun elem =>
    (orSetElemEventKey elem, (toJson elem.val).compress))
  checkConsistentPairs pairs "conflicting OR-Set add tag identity"

def mergeOrSetJson (a b : OrSetJson) : OrSetJson :=
  let mergedTombstones := dedupeByKey orSetTagKey (a.tombstones ++ b.tombstones)
  let tombstoneKeys := mergedTombstones.map orSetTagKey
  let mergedElements := dedupeByKey orSetElemEventKey (a.elements ++ b.elements)
  let filteredElements := mergedElements.filter
    (fun elem => not (tombstoneKeys.contains (orSetTagKey elem.tag)))
  { elements := sortByKey orSetElemSortKey filteredElements
    tombstones := sortByKey orSetTagKey mergedTombstones }

def handleOrSetMerge (aJson bJson : Json) : Except String String := do
  let a : OrSetJson ← fromJson? aJson
  let b : OrSetJson ← fromJson? bJson
  validateOrSetHlcBounds a
  validateOrSetHlcBounds b
  assertOrSetConsistent (a.elements ++ b.elements)
  let out := mergeOrSetJson a b
  pure (resultLine (toJson out))

def mvEventKey (value : MvValueJson) : String :=
  hlcEventKey value.hlc value.site

def mvValueSortKey (value : MvValueJson) : String :=
  s!"{mvEventKey value}:{(toJson value.val).compress}"

def validateMvHlcBounds (input : MvJson) : Except String Unit := do
  for value in input.values do
    let _ ← toHlc value.hlc
    pure ()

def assertMvConsistent (values : List MvValueJson) : Except String Unit := do
  let pairs := values.map (fun value => (mvEventKey value, (toJson value.val).compress))
  checkConsistentPairs pairs "conflicting MV-Register event identity"

def mergeMvJson (a b : MvJson) : MvJson :=
  let merged := dedupeByKey mvEventKey (a.values ++ b.values)
  { values := sortByKey mvValueSortKey merged }

def handleMvMerge (aJson bJson : Json) : Except String String := do
  let a : MvJson ← fromJson? aJson
  let b : MvJson ← fromJson? bJson
  validateMvHlcBounds a
  validateMvHlcBounds b
  assertMvConsistent (a.values ++ b.values)
  let out := mergeMvJson a b
  pure (resultLine (toJson out))

def handleSqlGenerateOps (json : Json) : Except String String := do
  let cmd : SqlGenerateOpsCmd ← fromJson? json
  let out ← generateCrdtOps cmd.statement cmd.context
  pure (resultLine (toJson out))

def handleSqlBuildSelectPlan (json : Json) : Except String String := do
  let cmd : SqlBuildSelectPlanCmd ← fromJson? json
  let out := buildSelectPlan cmd.statement cmd.schema
  pure (resultLine (toJson out))

def handleLine (line : String) : Except String String := do
  let json ← Json.parse line
  let typ ← json.getObjValAs? String "type"
  match typ with
  | "lww_merge" =>
      let cmd : MergeCmd ← fromJson? json
      handleLwwMerge cmd.a cmd.b
  | "pn_merge" =>
      let cmd : MergeCmd ← fromJson? json
      handlePnMerge cmd.a cmd.b
  | "or_set_merge" =>
      let cmd : MergeCmd ← fromJson? json
      handleOrSetMerge cmd.a cmd.b
  | "mv_merge" =>
      let cmd : MergeCmd ← fromJson? json
      handleMvMerge cmd.a cmd.b
  | "sql_generate_ops" => handleSqlGenerateOps json
  | "sql_build_select_plan" => handleSqlBuildSelectPlan json
  | _ => throw s!"unsupported command: {typ}"

def emitLine (line : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr line
  stdout.putStr "\n"
  stdout.flush

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    pure ()
  else
    let trimmed := line.trimAscii
    if trimmed.isEmpty then
      loop stdin
    else
      match handleLine trimmed.copy with
      | Except.ok out => emitLine out
      | Except.error err =>
          emitLine <| (Json.mkObj [("error", toJson err)]).compress
      loop stdin

def main : IO Unit := do
  let stdin ← IO.getStdin
  loop stdin
