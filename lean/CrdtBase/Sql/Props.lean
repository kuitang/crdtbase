import CrdtBase.Sql.Defs

set_option autoImplicit false

namespace CrdtBase

def OpsHaveValidTags (ops : List EncodedCrdtOp) : Prop :=
  ∀ op, op ∈ ops → CrdtTypeTag.isValid op.typ

def OpsAreSyncable (ops : List EncodedCrdtOp) : Prop :=
  ∀ op, op ∈ ops → EncodedCrdtOp.isSyncable op

private theorem generated_tagsB_to_ops_have_valid_tags
    (ops : List EncodedCrdtOp)
    (hTags : generatedOpsHaveValidTagsB ops = true) :
    OpsHaveValidTags ops := by
  intro op hMem
  have hAll : ∀ x, x ∈ ops → CrdtTypeTag.isValidb x.typ = true := by
    simpa [generatedOpsHaveValidTagsB] using (List.all_eq_true.mp hTags)
  have hTagBool : CrdtTypeTag.isValidb op.typ = true := hAll op hMem
  exact decide_eq_true_eq.mp (by simpa [CrdtTypeTag.isValidb] using hTagBool)

private theorem generated_syncB_to_ops_are_syncable
    (ops : List EncodedCrdtOp)
    (hSync : generatedOpsAreSyncableB ops = true) :
    OpsAreSyncable ops := by
  intro op hMem
  have hAll : ∀ x, x ∈ ops → EncodedCrdtOp.isSyncableb x = true := by
    simpa [generatedOpsAreSyncableB] using (List.all_eq_true.mp hSync)
  have hSyncBool : EncodedCrdtOp.isSyncableb op = true := hAll op hMem
  exact decide_eq_true_eq.mp (by simpa [EncodedCrdtOp.isSyncableb] using hSyncBool)

private theorem validateGeneratedOps_type_sound
    (rawOps out : List EncodedCrdtOp)
    (h : validateGeneratedOps rawOps = Except.ok out) :
    OpsHaveValidTags out := by
  unfold validateGeneratedOps at h
  by_cases hTags : generatedOpsHaveValidTagsB rawOps = true
  · by_cases hSync : generatedOpsAreSyncableB rawOps = true
    · simp [hTags, hSync] at h
      cases h
      exact generated_tagsB_to_ops_have_valid_tags rawOps hTags
    · simp [hTags, hSync] at h
  · simp [hTags] at h

private theorem validateGeneratedOps_syncable
    (rawOps out : List EncodedCrdtOp)
    (h : validateGeneratedOps rawOps = Except.ok out) :
    OpsAreSyncable out := by
  unfold validateGeneratedOps at h
  by_cases hTags : generatedOpsHaveValidTagsB rawOps = true
  · by_cases hSync : generatedOpsAreSyncableB rawOps = true
    · simp [hTags, hSync] at h
      cases h
      exact generated_syncB_to_ops_are_syncable rawOps hSync
    · simp [hTags, hSync] at h
  · simp [hTags] at h

/-- A batch is type-sound when every emitted op carries one of the supported CRDT tags. -/
theorem write_ops_type_sound
    (statement : SqlWriteStatement)
    (context : SqlGenerationContext)
    (ops : List EncodedCrdtOp)
    (hGen : generateCrdtOps statement context = Except.ok ops)
    : OpsHaveValidTags ops := by
  unfold generateCrdtOps at hGen
  cases hCore : generateCrdtOpsCore statement context with
  | error err =>
      simp [hCore] at hGen
      cases hGen
  | ok rawOps =>
      simp [hCore] at hGen
      exact validateGeneratedOps_type_sound rawOps ops hGen

/-- A batch is syncable when each emitted op carries non-empty sync-critical identifiers. -/
theorem write_ops_syncable
    (statement : SqlWriteStatement)
    (context : SqlGenerationContext)
    (ops : List EncodedCrdtOp)
    (hGen : generateCrdtOps statement context = Except.ok ops)
    : OpsAreSyncable ops := by
  unfold generateCrdtOps at hGen
  cases hCore : generateCrdtOpsCore statement context with
  | error err =>
      simp [hCore] at hGen
      cases hGen
  | ok rawOps =>
      simp [hCore] at hGen
      exact validateGeneratedOps_syncable rawOps ops hGen

/-- Restatement of syncability as explicit non-empty field constraints for every op. -/
theorem no_nonsync_for_valid_crdt_writes
    (statement : SqlWriteStatement)
    (context : SqlGenerationContext)
    (ops : List EncodedCrdtOp)
    (hGen : generateCrdtOps statement context = Except.ok ops)
    : ∀ op, op ∈ ops → op.tbl ≠ "" ∧ op.col ≠ "" ∧ op.hlc ≠ "" ∧ op.site ≠ "" := by
  simpa [OpsAreSyncable] using write_ops_syncable statement context ops hGen

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
