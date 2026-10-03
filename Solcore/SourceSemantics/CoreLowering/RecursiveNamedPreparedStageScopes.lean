import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSpecializationMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection

/-! The real named codebook entry selects the original analyzed sidecar for
the actual specialized source view. The registry also retains the existing
anonymous selections. This is static invocation provenance; it supplies no
body execution law or native closure capture relation. The current recursive
stage trace has no global application rule, which is a separate boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
open Frontend SourceInference SourceCoreStageContracts
open CallContractCertificates CallEntryCertificates

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- This compares the complete selected specialization, rather than its key
or erased parameter/result types. -/
theorem sidecar_caller {plan : Plan} {key : Key} {sidecar : Sidecar}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : prepareSidecar plan key = .ok sidecar)
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    sidecar.caller = row := by
  unfold prepareSidecar at prepared
  simp only [selected, Except.mapError, bind, Except.bind] at prepared
  obtain ⟨_, _, prepared⟩ := bind_ok prepared
  split at prepared
  · cases prepared
  · split at prepared
    · cases prepared; rfl
    · cases prepared

inductive Selected (compiled : SourceCoreUnifiedCompilation.Compiled)
    (native : SourceCoreGeneralFunctions.CallableContext) :
    Dynamic.Closure → Staging.Recursive.Scope → Prop where
  | anonymous {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}
      (receipt : RecursiveStageRegistry.Selected compiled.sourceProgram compiled.indexed.base.plan native.table function scope) :
      Selected compiled native function scope
  | named {row : SourceSpecialization.SpecializedFunction}
      (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
      (sidecar : Sidecar)
      (issued : prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar)
      (same : sidecar.caller = row) :
      Selected compiled native prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view)

/-- Both cases use the same actual artifact and original plan. The prepared
table equation is kept with the registry, so an arbitrary table is not used
as the public invocation registry. -/
def registry {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (_actual : RecursiveNamedPreparedStageContracts.Prepared compiled native) : Staging.Recursive.Registry where
  Closure := Selected compiled native
  source := by
    intro function scope related
    cases related with
    | anonymous receipt => exact (RecursiveStageRegistry.registry _ _ _).source receipt
    | named => rfl
  context := by
    intro function scope related
    cases related with
    | anonymous receipt => exact (RecursiveStageRegistry.registry _ _ _).context receipt
    | named => rfl
  evidence := by
    intro function scope related
    cases related with
    | anonymous receipt => exact (RecursiveStageRegistry.registry _ _ _).evidence receipt
    | named => rfl

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {native : SourceCoreGeneralFunctions.CallableContext}
  (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan row.key = .ok row)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named row.key))

include actual prepared record descriptor in
/-- The descriptor's authenticated named contract supplies its real sidecar.
The complete plan record identifies that sidecar with the actual source view's
specialization, including all original stage flags and solved requirements. -/
theorem selected_of_descriptor :
    ∃ sidecar : Sidecar,
      prepareSidecar compiled.indexed.base.plan row.key = .ok sidecar ∧ sidecar.caller = row ∧
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) := by
  obtain ⟨entry, member, origin, _⟩ := descriptor_entry descriptor
  have authenticated := actual.entries_authenticated entry member
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | named issued =>
    obtain ⟨receipt⟩ := named_of_accepted issued
    have same := sidecar_caller receipt.prepared record
    exact ⟨receipt.sidecar, receipt.prepared, same, .named prepared receipt.sidecar receipt.prepared same⟩

include actual prepared record descriptor in
/-- The scope retains the exact original analysis and both substitution
components. Named views have no lexical local instantiation. -/
theorem original_stages :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).origin.declarationSubstitution = row.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).origin.localSubstitution = [] ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).guards.stages.callerReturnComptime = row.function.returnComptime ∧
      SourceStageAnalysis.analyzeFunction row.function = .ok row.stageAnalysis := by
  obtain ⟨sidecar, _, same, selected⟩ := selected_of_descriptor actual prepared record descriptor
  exact ⟨sidecar, selected, by simp only [RecursiveStageRegistry.scope_declarationSubstitution, same],
    rfl, by simp only [RecursiveStageRegistry.scope_returnMarker, same], by simpa only [same] using sidecar.analyzed⟩

include actual prepared record descriptor in
/-- The full resolved source evidence is passed to the callee scope without
recomputing it from a descriptor or native type. -/
theorem evidence_preserved :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).evidence =
        CallableNamedMetadata.environment prepared.available := by
  obtain ⟨sidecar, _, _, selected⟩ := selected_of_descriptor actual prepared record descriptor
  exact ⟨sidecar, selected, rfl⟩

include actual prepared record descriptor in
/-- Independent source validity provides the invocation frame and covers the
complete evidence context. Table authentication itself supplies no typing. -/
theorem source_frame_preserved
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (range : ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) row.parameterSubstitution) :
    ∃ sidecar : Sidecar,
      (registry actual).Closure prepared.view (RecursiveStageRegistry.scope sidecar [] prepared.view) ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).source = row.function.typedBody ∧
      (RecursiveStageRegistry.scope sidecar [] prepared.view).context =
        (RecursiveNamedSpecializationBodyFacts.bodyInstance compiled.sourceProgram row).context ∧
      prepared.view.evidence.Covers (RecursiveStageRegistry.scope sidecar [] prepared.view).context ∧
      Staging.FunctionHasStages row.function := by
  obtain ⟨sidecar, _, _, selected⟩ := selected_of_descriptor actual prepared record descriptor
  have frame := prepared.source_frame wellFormed range
  exact ⟨sidecar, selected, frame.source, frame.context, by change Dynamic.EvidenceEnvironment.Covers prepared.view.context prepared.view.evidence; rw [frame.context]; exact frame.covers,
    prepared.has_stages wellFormed⟩

include actual prepared descriptor in
/-- The named descriptor's static origin is attached to the same generic
instantiation and full resolved evidence. The underlying native code/capture
meaning is an additional payload relation, independent of this receipt. -/
theorem global_origin
    (target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedMetadata.instantiation row) = .ok row.key) (raw : Core.Value) :
    CallableLedger.OriginRep compiled.indexed.base.plan native.table
      (.global ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩)
      (.pair raw (.word descriptor.id)) :=
  RecursiveStageProjection.named_origin (function := ⟨CallableNamedMetadata.instantiation row, prepared.view.evidence⟩) actual.accepted descriptor target raw
end Actual

/-- Existing anonymous factory selections remain available in the same
registry. Their full cumulative local substitution is unchanged. -/
theorem anonymous_preserved {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}
    (selected : RecursiveStageRegistry.Selected compiled.sourceProgram compiled.indexed.base.plan native.table function scope) :
    (registry actual).Closure function scope := .anonymous selected

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
