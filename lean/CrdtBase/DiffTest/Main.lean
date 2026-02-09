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

structure SqlEvalContextCmd where
  schema : List SqlTableSchema
  site : Option String := none
  hlcSequence : Option (List String) := none
  removeTags : Option (List SetRemoveTag) := none

instance : FromJson SqlEvalContextCmd where
  fromJson? json := do
    let schema ← json.getObjValAs? (List SqlTableSchema) "schema"
    let site := (json.getObjValAs? (Option String) "site").toOption.getD none
    let hlcSequence :=
      (json.getObjValAs? (Option (List String)) "hlcSequence").toOption.getD none
    let removeTags :=
      (json.getObjValAs? (Option (List SetRemoveTag)) "removeTags").toOption.getD none
    pure { schema, site, hlcSequence, removeTags }

instance : ToJson SqlEvalContextCmd where
  toJson context := Json.mkObj [
    ("schema", toJson context.schema),
    ("site", toJson context.site),
    ("hlcSequence", toJson context.hlcSequence),
    ("removeTags", toJson context.removeTags)
  ]

structure EvalCounterState where
  inc : List PnEntryJson
  dec : List PnEntryJson
  deriving FromJson, ToJson

structure EvalOrElement where
  val : Json
  hlc : String
  site : String

instance : FromJson EvalOrElement where
  fromJson? json := do
    let val ← json.getObjVal? "val"
    let hlc ← json.getObjValAs? String "hlc"
    let site ← json.getObjValAs? String "site"
    pure { val, hlc := canonicalizeHlcHex hlc, site }

instance : ToJson EvalOrElement where
  toJson value := Json.mkObj [
    ("val", value.val),
    ("hlc", toJson value.hlc),
    ("site", toJson value.site)
  ]

structure EvalOrState where
  elements : List EvalOrElement
  tombstones : List SetRemoveTag
  deriving FromJson, ToJson

structure EvalMvValue where
  val : Json
  hlc : String
  site : String

instance : FromJson EvalMvValue where
  fromJson? json := do
    let val ← json.getObjVal? "val"
    let hlc ← json.getObjValAs? String "hlc"
    let site ← json.getObjValAs? String "site"
    pure { val, hlc := canonicalizeHlcHex hlc, site }

instance : ToJson EvalMvValue where
  toJson value := Json.mkObj [
    ("val", value.val),
    ("hlc", toJson value.hlc),
    ("site", toJson value.site)
  ]

structure EvalMvState where
  values : List EvalMvValue
  deriving FromJson, ToJson

inductive EvalColumnState where
  | lww (val : Json) (hlc : String) (site : String)
  | pnCounter (state : EvalCounterState)
  | orSet (state : EvalOrState)
  | mvRegister (state : EvalMvState)

instance : FromJson EvalColumnState where
  fromJson? json := do
    let typ ← json.getObjValAs? Nat "typ"
    match typ with
    | 1 =>
        let val ← json.getObjVal? "val"
        let hlc ← json.getObjValAs? String "hlc"
        let site ← json.getObjValAs? String "site"
        pure (.lww val (canonicalizeHlcHex hlc) site)
    | 2 =>
        let inc ← json.getObjValAs? (List PnEntryJson) "inc"
        let dec ← json.getObjValAs? (List PnEntryJson) "dec"
        pure (.pnCounter { inc, dec })
    | 3 =>
        let elements ← json.getObjValAs? (List EvalOrElement) "elements"
        let tombstonesRaw ← json.getObjValAs? (List SetRemoveTag) "tombstones"
        let tombstones := tombstonesRaw.map (fun tag => { tag with hlc := canonicalizeHlcHex tag.hlc })
        pure (.orSet { elements, tombstones })
    | 4 =>
        let values ← json.getObjValAs? (List EvalMvValue) "values"
        pure (.mvRegister { values })
    | other => throw s!"unsupported eval column typ {other}"

instance : ToJson EvalColumnState where
  toJson
    | .lww val hlc site =>
        Json.mkObj [
          ("typ", toJson (1 : Nat)),
          ("val", val),
          ("hlc", toJson hlc),
          ("site", toJson site)
        ]
    | .pnCounter state =>
        Json.mkObj [
          ("typ", toJson (2 : Nat)),
          ("inc", toJson state.inc),
          ("dec", toJson state.dec)
        ]
    | .orSet state =>
        Json.mkObj [
          ("typ", toJson (3 : Nat)),
          ("elements", toJson state.elements),
          ("tombstones", toJson state.tombstones)
        ]
    | .mvRegister state =>
        Json.mkObj [
          ("typ", toJson (4 : Nat)),
          ("values", toJson state.values)
        ]

structure EvalColumn where
  column : String
  state : EvalColumnState
  deriving FromJson, ToJson

structure EvalRow where
  table : String
  key : Json
  columns : List EvalColumn
  deriving FromJson, ToJson

structure SqlEvalStateCmd where
  rows : List EvalRow
  deriving FromJson, ToJson

structure SqlEvalCmd where
  type : String
  statement : Json
  context : SqlEvalContextCmd
  state : SqlEvalStateCmd
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

def findTableSchema? (schema : List SqlTableSchema) (table : String) : Option SqlTableSchema :=
  schema.find? (fun entry => decide (entry.table = table))

def requireTableSchema (schema : List SqlTableSchema) (table : String) : Except String SqlTableSchema := do
  match findTableSchema? schema table with
  | some tableSchema => pure tableSchema
  | none => throw s!"unknown table '{table}'"

def scalarJsonType? (value : Json) : Option String :=
  match value with
  | .null => some "null"
  | .str _ => some "string"
  | .num _ => some "number"
  | .bool _ => some "boolean"
  | _ => none

def compareJsonScalars? (left right : Json) : Option Int :=
  match left, right with
  | .num l, .num r =>
      let lf := l.toFloat
      let rf := r.toFloat
      if lf < rf then some (-1) else if lf > rf then some 1 else some 0
  | .str l, .str r =>
      if l < r then some (-1) else if l > r then some 1 else some 0
  | .bool l, .bool r =>
      if l = r then some 0 else if l then some 1 else some (-1)
  | .null, .null => some 0
  | _, _ => none

def evalCondition (actual? : Option Json) (op : SqlComparisonOp) (expected : Json) : Bool :=
  match actual? with
  | none => false
  | some actual =>
      match compareJsonScalars? actual expected with
      | some cmp =>
          match op with
          | .eq => cmp == 0
          | .ne => cmp != 0
          | .lt => decide (cmp < 0)
          | .gt => decide (cmp > 0)
          | .le => decide (cmp ≤ 0)
          | .ge => decide (cmp ≥ 0)
      | none =>
          match actual with
          | .arr values =>
              match op with
              | .eq => values.any (fun value => value.compress == expected.compress)
              | .ne => values.all (fun value => value.compress != expected.compress)
              | _ => false
          | _ =>
              match op with
              | .ne =>
                  match scalarJsonType? actual, scalarJsonType? expected with
                  | some _, some _ => true
                  | _, _ => false
              | _ => false

def evalColumnTypeTag (state : EvalColumnState) : Nat :=
  match state with
  | .lww .. => 1
  | .pnCounter _ => 2
  | .orSet _ => 3
  | .mvRegister _ => 4

def compareEventKey (hlcA siteA hlcB siteB : String) : Ordering :=
  match compare hlcA hlcB with
  | .eq => compare siteA siteB
  | ord => ord

def lookupColumnState (columns : List EvalColumn) (column : String) : Option EvalColumnState :=
  (columns.find? (fun entry => decide (entry.column = column))).map (·.state)

def upsertColumnState (columns : List EvalColumn) (column : String) (state : EvalColumnState) : List EvalColumn :=
  let rec go (acc : List EvalColumn) (rest : List EvalColumn) : List EvalColumn :=
    match rest with
    | [] => (acc.reverse ++ [{ column, state }])
    | entry :: tail =>
        if entry.column = column then
          acc.reverse ++ ({ column, state } :: tail)
        else
          go (entry :: acc) tail
  go [] columns

def upsertRow (rows : List EvalRow) (table : String) (key : Json) (nextColumns : List EvalColumn)
    : List EvalRow :=
  let rec go (acc : List EvalRow) (rest : List EvalRow) : List EvalRow :=
    match rest with
    | [] => (acc.reverse ++ [({ table := table, key := key, columns := nextColumns } : EvalRow)])
    | row :: tail =>
        if row.table == table && row.key.compress == key.compress then
          acc.reverse ++ (({ table := table, key := key, columns := nextColumns } : EvalRow) :: tail)
        else
          go (row :: acc) tail
  go [] rows

def lookupPnNat (entries : List PnEntryJson) (site : String) : Nat :=
  entries.foldl (fun acc entry => if entry.site = site then acc + entry.n else acc) 0

def setPnNat (entries : List PnEntryJson) (site : String) (value : Nat) : List PnEntryJson :=
  let filtered := entries.filter (fun entry => decide (entry.site ≠ site))
  if value = 0 then filtered else { site, n := value } :: filtered

def jsonToNat? (value : Json) : Option Nat :=
  match value with
  | .num n =>
      if n.exponent = 0 then
        if n.mantissa >= 0 then
          some n.mantissa.toNat
        else
          none
      else
        none
  | _ => none

def normalizeOrSetState (state : EvalOrState) : Except String EvalOrState := do
  let eventPairs := state.elements.map (fun entry =>
    (s!"{entry.hlc}:{entry.site}", entry.val.compress))
  checkConsistentPairs eventPairs "conflicting OR-Set add tag identity"
  let canonicalTombstones :=
    state.tombstones.map (fun tag => { tag with hlc := canonicalizeHlcHex tag.hlc })
  let tombstones := dedupeByKey (fun tag => s!"{tag.hlc}:{tag.site}") canonicalTombstones
  let tombstoneKeys := tombstones.map (fun tag => s!"{tag.hlc}:{tag.site}")
  let elements := dedupeByKey (fun entry => s!"{entry.hlc}:{entry.site}") state.elements
    |>.filter (fun entry => !(tombstoneKeys.contains s!"{entry.hlc}:{entry.site}"))
  pure {
    elements := sortByKey (fun entry => s!"{entry.hlc}:{entry.site}:{entry.val.compress}") elements
    tombstones := sortByKey (fun tag => s!"{tag.hlc}:{tag.site}") tombstones
  }

def normalizeMvState (state : EvalMvState) : Except String EvalMvState := do
  let eventPairs := state.values.map (fun entry =>
    (s!"{entry.hlc}:{entry.site}", entry.val.compress))
  checkConsistentPairs eventPairs "conflicting MV-Register event identity"
  let values := dedupeByKey (fun entry => s!"{entry.hlc}:{entry.site}") state.values
  pure {
    values := sortByKey (fun entry => s!"{entry.hlc}:{entry.site}:{entry.val.compress}") values
  }

def normalizeEvalColumnState (state : EvalColumnState) : Except String EvalColumnState := do
  match state with
  | .lww val hlc site => pure (.lww val (canonicalizeHlcHex hlc) site)
  | .pnCounter counter => pure (.pnCounter counter)
  | .orSet orState => pure (.orSet (← normalizeOrSetState orState))
  | .mvRegister mvState => pure (.mvRegister (← normalizeMvState mvState))

def normalizeEvalRows (rows : List EvalRow) : Except String (List EvalRow) := do
  rows.mapM (fun row => do
    let columns ← row.columns.mapM (fun column => do
      let state ← normalizeEvalColumnState column.state
      pure { column := column.column, state })
    pure { table := row.table, key := row.key, columns })

def mergeLwwValue (current incoming : Json × String × String) : Except String (Json × String × String) := do
  if current.2.1 == incoming.2.1 && current.2.2 == incoming.2.2 &&
      current.1.compress != incoming.1.compress then
    throw "conflicting LWW event identity: same (hlc, site) with different payloads"
  match compareEventKey current.2.1 current.2.2 incoming.2.1 incoming.2.2 with
  | .lt => pure incoming
  | _ => pure current

def applyOpToRows (rows : List EvalRow) (op : EncodedCrdtOp) : Except String (List EvalRow) := do
  let currentRow? := rows.find? (fun row => row.table == op.tbl && row.key.compress == op.key.compress)
  let currentColumns := currentRow?.map (·.columns) |>.getD []
  let currentColumn? := lookupColumnState currentColumns op.col
  let opHlc := canonicalizeHlcHex op.hlc
  let nextState ←
    match op.typ with
    | 1 =>
        match currentColumn? with
        | none => pure (.lww op.val opHlc op.site)
        | some (.lww value hlc site) => do
            let merged ← mergeLwwValue (value, hlc, site) (op.val, opHlc, op.site)
            pure (.lww merged.1 merged.2.1 merged.2.2)
        | some other =>
            throw s!"column '{op.tbl}.{op.col}' was previously typ {evalColumnTypeTag other}, got typ 1"
    | 2 =>
        match op.val.getObjValAs? String "d", op.val.getObjVal? "n" with
        | Except.ok direction, Except.ok nJson =>
            let amount ←
              match jsonToNat? nJson with
              | some n => pure n
              | none => throw s!"invalid PN-Counter payload for {op.tbl}.{op.col}"
            match currentColumn? with
            | none =>
                let counter := if direction == "inc"
                  then { inc := setPnNat [] op.site amount, dec := [] }
                  else if direction == "dec"
                    then { inc := [], dec := setPnNat [] op.site amount }
                    else { inc := [], dec := [] }
                if direction == "inc" || direction == "dec" then
                  pure (.pnCounter counter)
                else
                  throw s!"invalid PN-Counter payload for {op.tbl}.{op.col}"
            | some (.pnCounter counter) =>
                let updated :=
                  if direction == "inc" then
                    { inc := setPnNat counter.inc op.site (lookupPnNat counter.inc op.site + amount)
                      dec := counter.dec }
                  else if direction == "dec" then
                    { inc := counter.inc
                      dec := setPnNat counter.dec op.site (lookupPnNat counter.dec op.site + amount) }
                  else counter
                if direction == "inc" || direction == "dec" then
                  pure (.pnCounter updated)
                else
                  throw s!"invalid PN-Counter payload for {op.tbl}.{op.col}"
            | some other =>
                throw s!"column '{op.tbl}.{op.col}' was previously typ {evalColumnTypeTag other}, got typ 2"
        | _, _ => throw s!"invalid PN-Counter payload for {op.tbl}.{op.col}"
    | 3 =>
        match op.val.getObjValAs? String "a" with
        | Except.ok "add" =>
            let value ← op.val.getObjVal? "val"
            match currentColumn? with
            | none =>
                let normalized ← normalizeOrSetState {
                  elements := [{ val := value, hlc := opHlc, site := op.site }]
                  tombstones := []
                }
                pure (.orSet normalized)
            | some (.orSet state) =>
                let normalized ← normalizeOrSetState {
                  elements := state.elements ++ [{ val := value, hlc := opHlc, site := op.site }]
                  tombstones := state.tombstones
                }
                pure (.orSet normalized)
            | some other =>
                throw s!"column '{op.tbl}.{op.col}' was previously typ {evalColumnTypeTag other}, got typ 3"
        | Except.ok "rmv" =>
            let tagsRaw ← op.val.getObjValAs? (List SetRemoveTag) "tags"
            let tags := tagsRaw.map (fun tag => { tag with hlc := canonicalizeHlcHex tag.hlc })
            match currentColumn? with
            | none =>
                let normalized ← normalizeOrSetState {
                  elements := []
                  tombstones := tags
                }
                pure (.orSet normalized)
            | some (.orSet state) =>
                let normalized ← normalizeOrSetState {
                  elements := state.elements
                  tombstones := state.tombstones ++ tags
                }
                pure (.orSet normalized)
            | some other =>
                throw s!"column '{op.tbl}.{op.col}' was previously typ {evalColumnTypeTag other}, got typ 3"
        | _ => throw s!"invalid OR-Set payload for {op.tbl}.{op.col}"
    | 4 =>
        match scalarJsonType? op.val with
        | none => throw s!"invalid MV-Register payload for {op.tbl}.{op.col}"
        | some _ =>
            match currentColumn? with
            | none =>
                let normalized ← normalizeMvState {
                  values := [{ val := op.val, hlc := opHlc, site := op.site }]
                }
                pure (.mvRegister normalized)
            | some (.mvRegister state) =>
                let normalized ← normalizeMvState {
                  values := state.values ++ [{ val := op.val, hlc := opHlc, site := op.site }]
                }
                pure (.mvRegister normalized)
            | some other =>
                throw s!"column '{op.tbl}.{op.col}' was previously typ {evalColumnTypeTag other}, got typ 4"
    | other => throw s!"unsupported CRDT op type {other}"

  let nextColumns := upsertColumnState currentColumns op.col nextState
  pure (upsertRow rows op.tbl op.key nextColumns)

def materializeRow (row : EvalRow) : List (String × Json) :=
  row.columns.map (fun column =>
    match column.state with
    | .lww val _ _ => (column.column, val)
    | .pnCounter counter =>
        let inc := counter.inc.foldl (fun acc entry => acc + entry.n) 0
        let dec := counter.dec.foldl (fun acc entry => acc + entry.n) 0
        (column.column, toJson (Int.ofNat inc - Int.ofNat dec))
    | .orSet state =>
        let visible := state.elements.map (·.val)
        let deduped := dedupeByKey (fun value => value.compress) visible
        (column.column, Json.arr deduped.toArray)
    | .mvRegister state =>
        match state.values with
        | [single] => (column.column, single.val)
        | many => (column.column, Json.arr (many.map (·.val)).toArray))

def lookupMaterialized (values : List (String × Json)) (column : String) : Option Json :=
  (values.find? (fun entry => entry.1 = column)).map (·.2)

def selectOutputRow
    (columns : SelectColumns)
    (values : List (String × Json))
    : Json :=
  match columns with
  | .all => Json.mkObj values
  | .named selected =>
      let projected := selected.map (fun column =>
        match lookupMaterialized values column with
        | some value => (column, value)
        | none => (column, Json.null))
      Json.mkObj projected

def runSelectStatement
    (statement : SelectStatement)
    (schema : List SqlTableSchema)
    (rows : List EvalRow)
    : Except String Json := do
  let tableSchema ← requireTableSchema schema statement.table
  let plan := buildSelectPlan statement { partitionBy := tableSchema.partitionBy }
  let outputRows := rows.filterMap (fun row =>
    if row.table ≠ statement.table then
      none
    else
      let materialized := materializeRow row
      let values := (tableSchema.pk, row.key) :: materialized
      let keep := plan.filters.all (fun condition =>
        evalCondition (lookupMaterialized values condition.column) condition.op condition.value)
      if keep then
        some (selectOutputRow plan.columns values)
      else
        none)
  pure <| Json.mkObj [
    ("kind", toJson "read"),
    ("select", toJson plan),
    ("rows", Json.arr outputRows.toArray)
  ]

def writeStatementKind (statement : SqlWriteStatement) : String :=
  match statement with
  | .insert _ => "insert"
  | .update _ => "update"
  | .inc _ => "inc"
  | .dec _ => "dec"
  | .add _ => "add"
  | .remove _ => "remove"
  | .delete _ => "delete"

def applyOpsToRows (rows : List EvalRow) (ops : List EncodedCrdtOp) : Except String (List EvalRow) := do
  let rec loop (acc : List EvalRow) (rest : List EncodedCrdtOp) : Except String (List EvalRow) := do
    match rest with
    | [] => pure acc
    | op :: tail =>
        let next ← applyOpToRows acc op
        loop next tail
  loop rows ops

def runWriteStatement
    (statement : SqlWriteStatement)
    (context : SqlEvalContextCmd)
    (rows : List EvalRow)
    : Except String (Json × List EvalRow) := do
  let site ←
    match context.site with
    | some value => pure value
    | none => throw "write planning requires schema, site, and nextHlc"
  let hlcSequence ←
    match context.hlcSequence with
    | some values => pure values
    | none => throw "write planning requires schema, site, and nextHlc"
  let generationContext : SqlGenerationContext := {
    schema := context.schema
    site := site
    hlcSequence := hlcSequence
    removeTags := context.removeTags.getD []
  }
  let ops ← generateCrdtOps statement generationContext
  let nextRows ← applyOpsToRows rows ops
  let result := Json.mkObj [
    ("kind", toJson "write"),
    ("statementKind", toJson (writeStatementKind statement)),
    ("ops", toJson ops)
  ]
  pure (result, nextRows)

def decodeWriteStatement? (statement : Json) : Except String SqlWriteStatement := do
  let kind ← statement.getObjValAs? String "kind"
  match kind with
  | "insert" => pure (.insert (← fromJson? statement))
  | "update" => pure (.update (← fromJson? statement))
  | "inc" => pure (.inc (← fromJson? statement))
  | "dec" => pure (.dec (← fromJson? statement))
  | "add" => pure (.add (← fromJson? statement))
  | "remove" => pure (.remove (← fromJson? statement))
  | "delete" => pure (.delete (← fromJson? statement))
  | _ => throw s!"unsupported SQL eval statement kind '{kind}'"

def handleSqlEval (json : Json) : Except String String := do
  let cmd : SqlEvalCmd ← fromJson? json
  let kind ← cmd.statement.getObjValAs? String "kind"
  let schema := cmd.context.schema
  let rows ← normalizeEvalRows cmd.state.rows
  let (result, nextRows) ←
    if kind = "select" then
      let statement : SelectStatement ← fromJson? cmd.statement
      let result ← runSelectStatement statement schema rows
      pure (result, rows)
    else
      let statement ← decodeWriteStatement? cmd.statement
      runWriteStatement statement cmd.context rows
  let nextState := Json.mkObj [
    ("schema", toJson schema),
    ("rows", toJson nextRows)
  ]
  pure (resultLine (Json.mkObj [
    ("result", result),
    ("nextState", nextState)
  ]))

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
  | "sql_eval" => handleSqlEval json
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
