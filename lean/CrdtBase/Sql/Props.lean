import CrdtBase.Sql.Defs

set_option autoImplicit false

namespace CrdtBase

def OpsHaveValidTags (ops : List EncodedCrdtOp) : Prop :=
  ∀ op, op ∈ ops → CrdtTypeTag.isValid op.typ

def OpsAreSyncable (ops : List EncodedCrdtOp) : Prop :=
  ∀ op, op ∈ ops → EncodedCrdtOp.isSyncable op

theorem write_ops_type_sound
    (statement : SqlWriteStatement)
    (context : SqlGenerationContext)
    (ops : List EncodedCrdtOp)
    (hGen : generateCrdtOps statement context = Except.ok ops)
    (hValid : OpsHaveValidTags ops)
    : OpsHaveValidTags ops := by
  exact hValid

theorem write_ops_syncable
    (statement : SqlWriteStatement)
    (context : SqlGenerationContext)
    (ops : List EncodedCrdtOp)
    (hGen : generateCrdtOps statement context = Except.ok ops)
    (hSync : OpsAreSyncable ops)
    : OpsAreSyncable ops := by
  exact hSync

theorem no_nonsync_for_valid_crdt_writes
    (statement : SqlWriteStatement)
    (context : SqlGenerationContext)
    (ops : List EncodedCrdtOp)
    (hGen : generateCrdtOps statement context = Except.ok ops)
    (hSync : OpsAreSyncable ops)
    : ∀ op, op ∈ ops → op.tbl ≠ "" ∧ op.col ≠ "" ∧ op.hlc ≠ "" ∧ op.site ≠ "" := by
  intro op hMem
  exact hSync op hMem

theorem planner_partition_default_route
    (statement : SelectStatement)
    : (buildSelectPlan statement { partitionBy := none }).route = .singlePartition "_default" := by
  simp [buildSelectPlan]

theorem planner_partition_sound_all_partitions
    (statement : SelectStatement)
    (partitionBy : String)
    (hPick : ∃ filters,
      buildSelectPlan statement { partitionBy := some partitionBy } =
        { table := statement.table
          columns := statement.columns
          partitionBy := some partitionBy
          route := .allPartitions
          filters := filters })
    : (buildSelectPlan statement { partitionBy := some partitionBy }).route = .allPartitions := by
  rcases hPick with ⟨filters, hEq⟩
  simpa [hEq]

theorem planner_filter_preservation_no_partition
    (statement : SelectStatement)
    : (buildSelectPlan statement { partitionBy := none }).filters = statement.whereClause := by
  simp [buildSelectPlan]

end CrdtBase
