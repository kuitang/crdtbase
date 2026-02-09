import Lean

set_option autoImplicit false

namespace CrdtBase

open Lean

inductive SqlComparisonOp where
  | eq
  | ne
  | lt
  | gt
  | le
  | ge
  deriving DecidableEq

instance : FromJson SqlComparisonOp where
  fromJson?
    | .str "=" => pure .eq
    | .str "!=" => pure .ne
    | .str "<" => pure .lt
    | .str ">" => pure .gt
    | .str "<=" => pure .le
    | .str ">=" => pure .ge
    | .str op => throw s!"unsupported SQL comparison operator '{op}'"
    | json => throw s!"expected SQL comparison operator string, got {json}"

instance : ToJson SqlComparisonOp where
  toJson
    | .eq => toJson "="
    | .ne => toJson "!="
    | .lt => toJson "<"
    | .gt => toJson ">"
    | .le => toJson "<="
    | .ge => toJson ">="

structure SqlWhereCondition where
  column : String
  op : SqlComparisonOp
  value : Json

instance : FromJson SqlWhereCondition where
  fromJson? json := do
    let column ← json.getObjValAs? String "column"
    let op ← json.getObjValAs? SqlComparisonOp "op"
    let value ← json.getObjVal? "value"
    pure { column, op, value }

instance : ToJson SqlWhereCondition where
  toJson condition := Json.mkObj [
    ("column", toJson condition.column),
    ("op", toJson condition.op),
    ("value", condition.value)
  ]

structure SqlAssignment where
  column : String
  value : Json

instance : FromJson SqlAssignment where
  fromJson? json := do
    let column ← json.getObjValAs? String "column"
    let value ← json.getObjVal? "value"
    pure { column, value }

instance : ToJson SqlAssignment where
  toJson assignment := Json.mkObj [
    ("column", toJson assignment.column),
    ("value", assignment.value)
  ]

inductive SelectColumns where
  | all
  | named (columns : List String)

instance : FromJson SelectColumns where
  fromJson?
    | .str "*" => pure .all
    | json@(.arr _) => do
        let columns : List String ← fromJson? json
        pure (.named columns)
    | json => throw s!"expected SELECT columns as '*' or string array, got {json}"

instance : ToJson SelectColumns where
  toJson
    | .all => toJson "*"
    | .named columns => toJson columns

structure SelectStatement where
  table : String
  columns : SelectColumns
  whereClause : List SqlWhereCondition := []

instance : FromJson SelectStatement where
  fromJson? json := do
    let kind ← json.getObjValAs? String "kind"
    if kind != "select" then
      throw s!"expected SELECT statement, got {kind}"
    let table ← json.getObjValAs? String "table"
    let columns ← json.getObjValAs? SelectColumns "columns"
    let whereOpt := (json.getObjValAs? (Option (List SqlWhereCondition)) "where").toOption.getD none
    pure { table, columns, whereClause := whereOpt.getD [] }

structure InsertStatement where
  table : String
  columns : List String
  values : List Json

instance : FromJson InsertStatement where
  fromJson? json := do
    let table ← json.getObjValAs? String "table"
    let columns ← json.getObjValAs? (List String) "columns"
    let values ← json.getObjValAs? (List Json) "values"
    pure { table, columns, values }

structure UpdateStatement where
  table : String
  assignments : List SqlAssignment
  whereClause : List SqlWhereCondition

instance : FromJson UpdateStatement where
  fromJson? json := do
    let table ← json.getObjValAs? String "table"
    let assignments ← json.getObjValAs? (List SqlAssignment) "assignments"
    let whereClause ← json.getObjValAs? (List SqlWhereCondition) "where"
    pure { table, assignments, whereClause }

structure CounterStatement where
  table : String
  column : String
  amount : Nat
  whereClause : List SqlWhereCondition

instance : FromJson CounterStatement where
  fromJson? json := do
    let table ← json.getObjValAs? String "table"
    let column ← json.getObjValAs? String "column"
    let amount ← json.getObjValAs? Nat "amount"
    let whereClause ← json.getObjValAs? (List SqlWhereCondition) "where"
    pure { table, column, amount, whereClause }

structure SetStatement where
  table : String
  column : String
  value : Json
  whereClause : List SqlWhereCondition

instance : FromJson SetStatement where
  fromJson? json := do
    let table ← json.getObjValAs? String "table"
    let column ← json.getObjValAs? String "column"
    let value ← json.getObjVal? "value"
    let whereClause ← json.getObjValAs? (List SqlWhereCondition) "where"
    pure { table, column, value, whereClause }

structure DeleteStatement where
  table : String
  whereClause : List SqlWhereCondition

instance : FromJson DeleteStatement where
  fromJson? json := do
    let table ← json.getObjValAs? String "table"
    let whereClause ← json.getObjValAs? (List SqlWhereCondition) "where"
    pure { table, whereClause }

inductive SqlWriteStatement where
  | insert (statement : InsertStatement)
  | update (statement : UpdateStatement)
  | inc (statement : CounterStatement)
  | dec (statement : CounterStatement)
  | add (statement : SetStatement)
  | remove (statement : SetStatement)
  | delete (statement : DeleteStatement)

instance : FromJson SqlWriteStatement where
  fromJson? json := do
    let kind ← json.getObjValAs? String "kind"
    match kind with
    | "insert" => pure (.insert (← fromJson? json))
    | "update" => pure (.update (← fromJson? json))
    | "inc" => pure (.inc (← fromJson? json))
    | "dec" => pure (.dec (← fromJson? json))
    | "add" => pure (.add (← fromJson? json))
    | "remove" => pure (.remove (← fromJson? json))
    | "delete" => pure (.delete (← fromJson? json))
    | _ => throw s!"statement '{kind}' does not generate CRDT ops"

inductive SqlColumnCrdt where
  | scalar
  | lww
  | pnCounter
  | orSet
  | mvRegister
  deriving DecidableEq

instance : FromJson SqlColumnCrdt where
  fromJson?
    | .str "scalar" => pure .scalar
    | .str "lww" => pure .lww
    | .str "pn_counter" => pure .pnCounter
    | .str "or_set" => pure .orSet
    | .str "mv_register" => pure .mvRegister
    | .str crdt => throw s!"unsupported SQL column CRDT '{crdt}'"
    | json => throw s!"expected SQL column CRDT string, got {json}"

instance : ToJson SqlColumnCrdt where
  toJson
    | .scalar => toJson "scalar"
    | .lww => toJson "lww"
    | .pnCounter => toJson "pn_counter"
    | .orSet => toJson "or_set"
    | .mvRegister => toJson "mv_register"

structure SqlColumnSchema where
  name : String
  crdt : SqlColumnCrdt

instance : FromJson SqlColumnSchema where
  fromJson? json := do
    let name ← json.getObjValAs? String "name"
    let crdt ← json.getObjValAs? SqlColumnCrdt "crdt"
    pure { name, crdt }

instance : ToJson SqlColumnSchema where
  toJson column := Json.mkObj [
    ("name", toJson column.name),
    ("crdt", toJson column.crdt)
  ]

structure SqlTableSchema where
  table : String
  pk : String
  partitionBy : Option String := none
  columns : List SqlColumnSchema

instance : FromJson SqlTableSchema where
  fromJson? json := do
    let table ← json.getObjValAs? String "table"
    let pk ← json.getObjValAs? String "pk"
    let partitionBy := (json.getObjValAs? (Option String) "partitionBy").toOption.getD none
    let columns ← json.getObjValAs? (List SqlColumnSchema) "columns"
    pure { table, pk, partitionBy, columns }

instance : ToJson SqlTableSchema where
  toJson tableSchema := Json.mkObj [
    ("table", toJson tableSchema.table),
    ("pk", toJson tableSchema.pk),
    ("partitionBy", toJson tableSchema.partitionBy),
    ("columns", toJson tableSchema.columns)
  ]

def canonicalizeHlcHex (raw : String) : String :=
  let withoutPrefix :=
    if raw.startsWith "0x" || raw.startsWith "0X" then
      raw.drop 2
    else
      raw
  let trimmed := (withoutPrefix.dropWhile (fun ch => ch = '0')).toString
  let body := if trimmed.isEmpty then "0" else trimmed
  s!"0x{body}"

structure SetRemoveTag where
  hlc : String
  site : String

instance : FromJson SetRemoveTag where
  fromJson? json := do
    let hlc ← json.getObjValAs? String "hlc"
    let site ← json.getObjValAs? String "site"
    pure { hlc, site }

instance : ToJson SetRemoveTag where
  toJson tag := Json.mkObj [
    ("hlc", toJson tag.hlc),
    ("site", toJson tag.site)
  ]

structure SqlGenerationContext where
  schema : List SqlTableSchema
  site : String
  hlcSequence : List String
  removeTags : List SetRemoveTag := []

instance : FromJson SqlGenerationContext where
  fromJson? json := do
    let schema ← json.getObjValAs? (List SqlTableSchema) "schema"
    let site ← json.getObjValAs? String "site"
    let hlcSequence ← json.getObjValAs? (List String) "hlcSequence"
    let removeTags := (json.getObjValAs? (Option (List SetRemoveTag)) "removeTags").toOption.getD none
      |>.getD []
    pure { schema, site, hlcSequence, removeTags }

structure SelectPlannerSchema where
  partitionBy : Option String := none

instance : FromJson SelectPlannerSchema where
  fromJson? json := do
    let partitionBy := (json.getObjValAs? (Option String) "partitionBy").toOption.getD none
    pure { partitionBy }

instance : ToJson SelectPlannerSchema where
  toJson schema := Json.mkObj [
    ("partitionBy", toJson schema.partitionBy)
  ]

structure EncodedCrdtOp where
  tbl : String
  key : Json
  col : String
  typ : Nat
  hlc : String
  site : String
  val : Json

instance : ToJson EncodedCrdtOp where
  toJson op := Json.mkObj [
    ("tbl", toJson op.tbl),
    ("key", op.key),
    ("col", toJson op.col),
    ("typ", toJson op.typ),
    ("hlc", toJson op.hlc),
    ("site", toJson op.site),
    ("val", op.val)
  ]

def CrdtTypeTag.isValid (tag : Nat) : Prop :=
  tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4

instance (tag : Nat) : Decidable (CrdtTypeTag.isValid tag) := by
  unfold CrdtTypeTag.isValid
  infer_instance

def EncodedCrdtOp.isSyncable (op : EncodedCrdtOp) : Prop :=
  op.tbl ≠ "" ∧ op.col ≠ "" ∧ op.hlc ≠ "" ∧ op.site ≠ ""

instance (op : EncodedCrdtOp) : Decidable (EncodedCrdtOp.isSyncable op) := by
  unfold EncodedCrdtOp.isSyncable
  infer_instance

inductive SelectQueryRoute where
  | singlePartition (partition : String)
  | allPartitions

instance : ToJson SelectQueryRoute where
  toJson
    | .singlePartition partition =>
        Json.mkObj [("kind", toJson "single_partition"), ("partition", toJson partition)]
    | .allPartitions =>
        Json.mkObj [("kind", toJson "all_partitions")]

structure SelectQueryPlan where
  table : String
  columns : SelectColumns
  partitionBy : Option String
  route : SelectQueryRoute
  filters : List SqlWhereCondition

instance : ToJson SelectQueryPlan where
  toJson plan :=
    Json.mkObj [
      ("table", toJson plan.table),
      ("columns", toJson plan.columns),
      ("partitionBy", toJson plan.partitionBy),
      ("route", toJson plan.route),
      ("filters", toJson plan.filters)
    ]

private def toPartitionKey (value : Json) : String :=
  match value with
  | .null => "NULL"
  | .str text => text
  | .num _ => value.compress
  | .bool b => if b then "true" else "false"
  | other => other.compress

private def lookupTableSchema (schema : List SqlTableSchema) (table : String)
    : Except String SqlTableSchema :=
  match schema.find? (fun entry => entry.table == table) with
  | some tableSchema => pure tableSchema
  | none => throw s!"unknown table '{table}'"

private def lookupColumnSchema (tableSchema : SqlTableSchema) (table column : String)
    : Except String SqlColumnSchema :=
  match tableSchema.columns.find? (fun entry => entry.name == column) with
  | some columnSchema => pure columnSchema
  | none => throw s!"unknown column '{column}' for table '{table}'"

private def assertPrimaryKeyValue (value : Json) (table pk : String) : Except String Json :=
  match value with
  | .str _ => pure value
  | .num _ => pure value
  | _ =>
      throw s!"primary key '{table}.{pk}' must be STRING or NUMBER, got {value.compress}"

private def findPrimaryKeyInWhere (whereClause : List SqlWhereCondition) (table pk : String)
    : Except String Json := do
  let condition? := whereClause.find? (fun condition => condition.column == pk && condition.op == .eq)
  match condition? with
  | none => throw s!"write on '{table}' requires WHERE {pk} = <value>"
  | some condition => assertPrimaryKeyValue condition.value table pk

private def nextHlc (hlcSequence : List String) : Except String (String × List String) :=
  match hlcSequence with
  | [] => throw "nextHlc called too many times"
  | hlc :: remaining => pure (hlc, remaining)

def createOp
    (table : String)
    (key : Json)
    (column : String)
    (typ : Nat)
    (hlc : String)
    (site : String)
    (val : Json)
    : EncodedCrdtOp :=
  { tbl := table
    key := key
    col := column
    typ := typ
    hlc := hlc
    site := site
    val := val }

private def createInsertColumnOp
    (statement : InsertStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (key : Json)
    (column : String)
    (value : Json)
    (hlcSequence : List String)
    : Except String (Option EncodedCrdtOp × List String) := do
  let columnSchema ← lookupColumnSchema tableSchema statement.table column
  match columnSchema.crdt with
  | .scalar => pure (none, hlcSequence)
  | .lww =>
      let (hlc, remaining) ← nextHlc hlcSequence
      pure (some (createOp statement.table key column 1 hlc site value), remaining)
  | .mvRegister =>
      let (hlc, remaining) ← nextHlc hlcSequence
      pure (some (createOp statement.table key column 4 hlc site value), remaining)
  | .pnCounter =>
      match value with
      | .num _ =>
          let (hlc, remaining) ← nextHlc hlcSequence
          let payload := Json.mkObj [("d", toJson "inc"), ("n", value)]
          pure (some (createOp statement.table key column 2 hlc site payload), remaining)
      | _ =>
          throw s!"INSERT for counter column '{statement.table}.{column}' requires NUMBER"
  | .orSet =>
      let (hlc, remaining) ← nextHlc hlcSequence
      let payload := Json.mkObj [("a", toJson "add"), ("val", value)]
      pure (some (createOp statement.table key column 3 hlc site payload), remaining)

private def createUpdateColumnOp
    (statement : UpdateStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (key : Json)
    (assignment : SqlAssignment)
    (hlcSequence : List String)
    : Except String (EncodedCrdtOp × List String) := do
  let columnSchema ← lookupColumnSchema tableSchema statement.table assignment.column
  match columnSchema.crdt with
  | .lww =>
      let (hlc, remaining) ← nextHlc hlcSequence
      pure (createOp statement.table key assignment.column 1 hlc site assignment.value, remaining)
  | .mvRegister =>
      let (hlc, remaining) ← nextHlc hlcSequence
      pure (createOp statement.table key assignment.column 4 hlc site assignment.value, remaining)
  | .scalar =>
      throw s!"UPDATE cannot target scalar column '{statement.table}.{assignment.column}'"
  | .pnCounter =>
      throw s!"UPDATE cannot target counter column '{statement.table}.{assignment.column}'; use INC/DEC"
  | .orSet =>
      throw s!"UPDATE cannot target set column '{statement.table}.{assignment.column}'; use ADD/REMOVE"

private def collectInsertOps
    (statement : InsertStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (key : Json)
    (pairs : List (String × Json))
    (hlcSequence : List String)
    (acc : List EncodedCrdtOp)
    : Except String (List EncodedCrdtOp × List String) := do
  match pairs with
  | [] => pure (acc.reverse, hlcSequence)
  | (column, value) :: tail =>
      if column == tableSchema.pk then
        collectInsertOps statement tableSchema site key tail hlcSequence acc
      else
        let (op?, remaining) ← createInsertColumnOp statement tableSchema site key column value hlcSequence
        match op? with
        | none => collectInsertOps statement tableSchema site key tail remaining acc
        | some op => collectInsertOps statement tableSchema site key tail remaining (op :: acc)

private def generateInsertOps
    (statement : InsertStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (hlcSequence : List String)
    : Except String (List EncodedCrdtOp × List String) := do
  if statement.columns.length != statement.values.length then
    throw s!"INSERT columns/values length mismatch ({statement.columns.length} columns, {statement.values.length} values)"
  let valuesByColumn := List.zip statement.columns statement.values
  let primaryValue? := valuesByColumn.find? (fun pair => pair.fst == tableSchema.pk)
  let primaryValue ←
    match primaryValue? with
    | none =>
        throw s!"INSERT into '{statement.table}' must include primary key column '{tableSchema.pk}'"
    | some pair => pure pair.snd
  let key ← assertPrimaryKeyValue primaryValue statement.table tableSchema.pk
  collectInsertOps statement tableSchema site key valuesByColumn hlcSequence []

private def collectUpdateOps
    (statement : UpdateStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (key : Json)
    (assignments : List SqlAssignment)
    (hlcSequence : List String)
    (acc : List EncodedCrdtOp)
    : Except String (List EncodedCrdtOp × List String) := do
  match assignments with
  | [] => pure (acc.reverse, hlcSequence)
  | assignment :: tail =>
      let (op, remaining) ← createUpdateColumnOp statement tableSchema site key assignment hlcSequence
      collectUpdateOps statement tableSchema site key tail remaining (op :: acc)

private def generateUpdateOps
    (statement : UpdateStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (hlcSequence : List String)
    : Except String (List EncodedCrdtOp × List String) := do
  let key ← findPrimaryKeyInWhere statement.whereClause statement.table tableSchema.pk
  collectUpdateOps statement tableSchema site key statement.assignments hlcSequence []

private def generateCounterOps
    (statement : CounterStatement)
    (direction : String)
    (tableSchema : SqlTableSchema)
    (site : String)
    (hlcSequence : List String)
    : Except String (List EncodedCrdtOp × List String) := do
  let key ← findPrimaryKeyInWhere statement.whereClause statement.table tableSchema.pk
  let columnSchema ← lookupColumnSchema tableSchema statement.table statement.column
  if columnSchema.crdt != .pnCounter then
    throw s!"column '{statement.table}.{statement.column}' is not a COUNTER"
  let (hlc, remaining) ← nextHlc hlcSequence
  let payload := Json.mkObj [("d", toJson direction), ("n", toJson statement.amount)]
  pure ([createOp statement.table key statement.column 2 hlc site payload], remaining)

private def generateSetAddOps
    (statement : SetStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (hlcSequence : List String)
    : Except String (List EncodedCrdtOp × List String) := do
  let key ← findPrimaryKeyInWhere statement.whereClause statement.table tableSchema.pk
  let columnSchema ← lookupColumnSchema tableSchema statement.table statement.column
  if columnSchema.crdt != .orSet then
    throw s!"column '{statement.table}.{statement.column}' is not a SET"
  let (hlc, remaining) ← nextHlc hlcSequence
  let payload := Json.mkObj [("a", toJson "add"), ("val", statement.value)]
  pure ([createOp statement.table key statement.column 3 hlc site payload], remaining)

private def generateSetRemoveOps
    (statement : SetStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (removeTags : List SetRemoveTag)
    (hlcSequence : List String)
    : Except String (List EncodedCrdtOp × List String) := do
  let key ← findPrimaryKeyInWhere statement.whereClause statement.table tableSchema.pk
  let columnSchema ← lookupColumnSchema tableSchema statement.table statement.column
  if columnSchema.crdt != .orSet then
    throw s!"column '{statement.table}.{statement.column}' is not a SET"
  if removeTags.isEmpty then
    pure ([], hlcSequence)
  else
    let (hlc, remaining) ← nextHlc hlcSequence
    let payload := Json.mkObj [("a", toJson "rmv"), ("tags", toJson removeTags)]
    pure ([createOp statement.table key statement.column 3 hlc site payload], remaining)

private def generateDeleteOps
    (statement : DeleteStatement)
    (tableSchema : SqlTableSchema)
    (site : String)
    (hlcSequence : List String)
    : Except String (List EncodedCrdtOp × List String) := do
  let key ← findPrimaryKeyInWhere statement.whereClause statement.table tableSchema.pk
  let (hlc, remaining) ← nextHlc hlcSequence
  pure ([createOp statement.table key "_deleted" 1 hlc site (toJson true)], remaining)

def generateCrdtOpsCore
    (statement : SqlWriteStatement)
    (context : SqlGenerationContext)
    : Except String (List EncodedCrdtOp) := do
  let tableName :=
    match statement with
    | .insert stmt => stmt.table
    | .update stmt => stmt.table
    | .inc stmt => stmt.table
    | .dec stmt => stmt.table
    | .add stmt => stmt.table
    | .remove stmt => stmt.table
    | .delete stmt => stmt.table
  let tableSchema ← lookupTableSchema context.schema tableName
  let result ←
    match statement with
    | .insert stmt =>
        generateInsertOps stmt tableSchema context.site context.hlcSequence
    | .update stmt =>
        generateUpdateOps stmt tableSchema context.site context.hlcSequence
    | .inc stmt =>
        generateCounterOps stmt "inc" tableSchema context.site context.hlcSequence
    | .dec stmt =>
        generateCounterOps stmt "dec" tableSchema context.site context.hlcSequence
    | .add stmt =>
        generateSetAddOps stmt tableSchema context.site context.hlcSequence
    | .remove stmt =>
        generateSetRemoveOps stmt tableSchema context.site context.removeTags context.hlcSequence
    | .delete stmt =>
        generateDeleteOps stmt tableSchema context.site context.hlcSequence
  pure result.fst

def CrdtTypeTag.isValidb (tag : Nat) : Bool :=
  decide (CrdtTypeTag.isValid tag)

def EncodedCrdtOp.isSyncableb (op : EncodedCrdtOp) : Bool :=
  decide (EncodedCrdtOp.isSyncable op)

def generatedOpsHaveValidTagsB (ops : List EncodedCrdtOp) : Bool :=
  ops.all (fun op => CrdtTypeTag.isValidb op.typ)

def generatedOpsAreSyncableB (ops : List EncodedCrdtOp) : Bool :=
  ops.all EncodedCrdtOp.isSyncableb

def validateGeneratedOps (ops : List EncodedCrdtOp) : Except String (List EncodedCrdtOp) :=
  if _ : generatedOpsHaveValidTagsB ops = true then
    if _ : generatedOpsAreSyncableB ops = true then
      pure ops
    else
      throw "internal error: generated non-syncable CRDT op"
  else
    throw "internal error: generated CRDT op with invalid type tag"

def generateCrdtOps
    (statement : SqlWriteStatement)
    (context : SqlGenerationContext)
    : Except String (List EncodedCrdtOp) := do
  let ops ← generateCrdtOpsCore statement context
  validateGeneratedOps ops

def pickPartitionCondition
    (whereClause : List SqlWhereCondition)
    (partitionBy : String)
    : Option (String × List SqlWhereCondition) :=
  let rec go (prefixRev remaining : List SqlWhereCondition) : Option (String × List SqlWhereCondition) :=
    match remaining with
    | [] => none
    | condition :: tail =>
        if condition.column == partitionBy && condition.op == .eq then
          some (toPartitionKey condition.value, prefixRev.reverse ++ tail)
        else
          go (condition :: prefixRev) tail
  go [] whereClause

def buildSelectPlan
    (statement : SelectStatement)
    (schema : SelectPlannerSchema := {})
    : SelectQueryPlan :=
  let whereClause := statement.whereClause
  match schema.partitionBy with
  | none =>
      { table := statement.table
        columns := statement.columns
        partitionBy := none
        route := .singlePartition "_default"
        filters := whereClause }
  | some partitionBy =>
      match pickPartitionCondition whereClause partitionBy with
      | none =>
          { table := statement.table
            columns := statement.columns
            partitionBy := some partitionBy
            route := .allPartitions
            filters := whereClause }
      | some (partition, remainingFilters) =>
          { table := statement.table
            columns := statement.columns
            partitionBy := some partitionBy
            route := .singlePartition partition
            filters := remainingFilters }

end CrdtBase
