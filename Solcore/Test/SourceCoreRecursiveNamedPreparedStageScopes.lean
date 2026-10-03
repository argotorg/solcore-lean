import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes

/-! Static consumers use the actual prepared table, complete plan row and
source view. The metadata receipt does not assert a global staged body run,
native capture correctness, source typing or an arbitrary table's authority. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Tests.SourceCoreRecursiveNamedPreparedStageScopes
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreStageContracts RecursiveNamedPreparedStageScopes

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {native : SourceCoreGeneralFunctions.CallableContext}
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan row.key = .ok row)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named row.key))

include actual prepared record descriptor in
theorem actual_named_scope :
    ∃ sidecar : Sidecar,
      prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar ∧ sidecar.caller = row ∧
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) :=
  selected_of_descriptor actual prepared record descriptor

include actual prepared record descriptor in
theorem full_original_metadata :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      sidecar.caller.function.typedBody = row.function.typedBody ∧
      sidecar.caller.function.solvedRequirements = row.function.solvedRequirements ∧
      sidecar.caller.assumptions = row.assumptions ∧ sidecar.caller.stageAnalysis = row.stageAnalysis ∧
      sidecar.caller.function.returnComptime = row.function.returnComptime := by
  obtain ⟨sidecar, _, same, selected⟩ := selected_of_descriptor actual prepared record descriptor
  exact ⟨sidecar, selected, by rw [same], by rw [same], by rw [same], by rw [same], by rw [same]⟩

include actual prepared record descriptor in
theorem named_substitutions_and_marker :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).origin.declarationSubstitution = row.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).origin.localSubstitution = [] ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).guards.stages.callerReturnComptime = row.function.returnComptime ∧
      SourceStageAnalysis.analyzeFunction row.function = .ok row.stageAnalysis :=
  original_stages actual prepared record descriptor

include actual prepared record descriptor in
theorem independent_source_admission
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).source = row.function.typedBody ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).context =
        (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context ∧
      prepared.view.evidence.Covers (RecursiveStageRegistry.scope sidecar [] prepared.view).context ∧
      Staging.FunctionHasStages row.function :=
  source_frame_preserved actual prepared record descriptor wellFormed range

include actual prepared record descriptor in
theorem resolved_dictionary :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).evidence =
        CallableNamedMetadata.environment prepared.available :=
  evidence_preserved actual prepared record descriptor

include actual prepared descriptor in
theorem actual_named_origin
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key) (raw : Core.Value) :
    CallableLedger.OriginRep compiled.indexed.base.plan native.table
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩)
      (.pair raw (.word descriptor.id)) :=
  global_origin actual prepared descriptor target raw
end Actual

theorem anonymous_scope_kept {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}
    (selected : RecursiveStageRegistry.Selected compiled.sourceProgram compiled.indexed.base.plan native.table function scope) :
    (registry actual).Closure function scope := anonymous_preserved actual selected

/-- The actual sidecar cannot be replaced by a different full record while
keeping the same successful plan selection. -/
theorem selected_full_record_unique {plan : Plan} {key : Key} {sidecar : Sidecar}
    {first second : SourceSpecialization.SpecializedFunction}
    (issued : prepareSidecar plan key = .ok sidecar)
    (one : SourceCompilationPlan.exactSpecialization plan key = .ok first)
    (two : SourceCompilationPlan.exactSpecialization plan key = .ok second) : first = second :=
  (sidecar_caller issued one).symm.trans (sidecar_caller issued two)

end Tests.SourceCoreRecursiveNamedPreparedStageScopes
