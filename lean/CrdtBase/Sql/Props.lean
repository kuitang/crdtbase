import CrdtBase.Sql.Defs

set_option autoImplicit false

namespace CrdtBase

def OpsHaveValidTags (ops : List EncodedCrdtOp) : Prop :=
  ∀ op, op ∈ ops → CrdtTypeTag.isValid op.typ

def OpsAreSyncable (ops : List EncodedCrdtOp) : Prop :=
  ∀ op, op ∈ ops → EncodedCrdtOp.isSyncable op

/-- A batch is type-sound when every emitted op carries one of the supported CRDT tags. -/
theorem write_ops_type_sound
    (ops : List EncodedCrdtOp)
    (hTag :
      ∀ op, op ∈ ops →
        op.typ = 1 ∨ op.typ = 2 ∨ op.typ = 3 ∨ op.typ = 4)
    : OpsHaveValidTags ops := by
  intro op hMem
  rcases hTag op hMem with h1 | h2 | h3 | h4
  · simpa [CrdtTypeTag.isValid, h1]
  · simpa [CrdtTypeTag.isValid, h2]
  · simpa [CrdtTypeTag.isValid, h3]
  · simpa [CrdtTypeTag.isValid, h4]

/-- A batch is syncable when each emitted op carries non-empty sync-critical identifiers. -/
theorem write_ops_syncable
    (ops : List EncodedCrdtOp)
    (hFields :
      ∀ op, op ∈ ops →
        op.tbl ≠ "" ∧ op.col ≠ "" ∧ op.hlc ≠ "" ∧ op.site ≠ "")
    : OpsAreSyncable ops := by
  intro op hMem
  exact hFields op hMem

/-- Restatement of syncability as explicit non-empty field constraints for every op. -/
theorem no_nonsync_for_valid_crdt_writes
    (ops : List EncodedCrdtOp)
    (hSync : OpsAreSyncable ops)
    : ∀ op, op ∈ ops → op.tbl ≠ "" ∧ op.col ≠ "" ∧ op.hlc ≠ "" ∧ op.site ≠ "" := by
  intro op hMem
  exact hSync op hMem

theorem planner_partition_default_route
    (statement : SelectStatement)
    : (buildSelectPlan statement { partitionBy := none }).route = .singlePartition "_default" := by
  simp [buildSelectPlan]

/-- If partition routing finds an equality predicate, planner routes to exactly that partition. -/
theorem planner_partition_sound
    (statement : SelectStatement)
    (partitionBy : String)
    (partition : String)
    (remainingFilters : List SqlWhereCondition)
    (hPick : pickPartitionCondition statement.whereClause partitionBy =
      some (partition, remainingFilters))
    : (buildSelectPlan statement { partitionBy := some partitionBy }).route =
        .singlePartition partition := by
  simp [buildSelectPlan, hPick]

theorem planner_partition_sound_all_partitions
    (statement : SelectStatement)
    (partitionBy : String)
    (hWhere : statement.whereClause = [])
    : (buildSelectPlan statement { partitionBy := some partitionBy }).route = .allPartitions := by
  have hPick : pickPartitionCondition [] partitionBy = none := by
    rfl
  simp [buildSelectPlan, hWhere, hPick]

/-- If no partition equality predicate is found, planner routes to all partitions. -/
theorem planner_partition_sound_all_partitions_of_no_match
    (statement : SelectStatement)
    (partitionBy : String)
    (hPick : pickPartitionCondition statement.whereClause partitionBy = none)
    : (buildSelectPlan statement { partitionBy := some partitionBy }).route = .allPartitions := by
  simp [buildSelectPlan, hPick]

/-- If partition routing picks a partition condition, planner filters equal the residual filters. -/
theorem planner_filter_preservation
    (statement : SelectStatement)
    (partitionBy : String)
    (partition : String)
    (remainingFilters : List SqlWhereCondition)
    (hPick : pickPartitionCondition statement.whereClause partitionBy =
      some (partition, remainingFilters))
    : (buildSelectPlan statement { partitionBy := some partitionBy }).filters = remainingFilters := by
  simp [buildSelectPlan, hPick]

theorem planner_filter_preservation_no_partition
    (statement : SelectStatement)
    : (buildSelectPlan statement { partitionBy := none }).filters = statement.whereClause := by
  simp [buildSelectPlan]

/-- If no partition equality predicate is found, planner preserves all original filters. -/
theorem planner_filter_preservation_all_partitions
    (statement : SelectStatement)
    (partitionBy : String)
    (hPick : pickPartitionCondition statement.whereClause partitionBy = none)
    : (buildSelectPlan statement { partitionBy := some partitionBy }).filters = statement.whereClause := by
  simp [buildSelectPlan, hPick]

end CrdtBase
