import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeDirectCellOrigins
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes

/-! The real direct closure member selects an independent recursive staging
scope. Its original sidecar comes from the actual descriptor's authenticated
lambda factory. Source, context, evidence, both substitutions and caller
staging markers are retained. This static selection contains no body execution
or guard acceptance law and does not extend the recursive trace's coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectStageScopeReceipts
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins

private theorem metadata_owner {caller : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok ()) :
    caller.function.typedBody.owner = caller.key.declaration := by
  by_cases ownership : SourceCompilationPlan.specializationOwnershipCoherent caller = true
  · change decide (caller.key.declaration = caller.declaration ∧
      caller.function.declaration = caller.declaration ∧
      caller.function.typedBody.owner = caller.declaration) = true at ownership
    have coherent := of_decide_eq_true ownership
    exact coherent.2.2.trans coherent.1.symm
  · unfold SourceCompilationPlan.validateSpecializationMetadataWith at accepted
    simp [ownership, throw, bind, Except.bind] at accepted

/-- Successful original preparation authenticates the sidecar's owner. -/
theorem sidecar_owner {plan : SourceCoreStageContracts.Plan}
    {key : SourceCoreStageContracts.Key} {sidecar : SourceCoreStageContracts.Sidecar}
    (accepted : SourceCoreStageContracts.prepareSidecar plan key = .ok sidecar) :
    sidecar.source.owner = sidecar.caller.key.declaration := by
  unfold SourceCoreStageContracts.prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      cases value
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
          exact metadata_owner valid
        · cases accepted

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Actual Code and canonical Source attribution recover their own sidecar
and recursive closure selection. No chosen sidecar is an input. -/
theorem code_scope {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative)
    (source : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  obtain ⟨site⟩ := RecursiveStageProjection.lambda_site_of_descriptor stages.accepted code.descriptor
  obtain ⟨sidecar, selected, _canonical⟩ := LambdaSourceAlignment.LambdaSource.canonical site.original
  have same := (CallContractCertificates.sidecar_of_accepted selected).2
  have alignedSite : AuthenticatedCallableLedger.LambdaSite compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sidecar.caller.key code.id code.active
      code.descriptor.id := by simpa only [same] using site
  have alignedSource : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      sidecar.caller.key code.active function.source := by simpa only [same] using source
  have owner : function.source.owner = sidecar.caller.key.declaration := by
    rw [source.source selected]
    exact sidecar_owner selected
  refine ⟨sidecar, selected, RecursiveStageRegistry.Selected.lambda
    (by simpa only [same] using selected) alignedSite alignedSource owner ?_⟩
  exact LambdaMetadataViews.lambda_origin alignedSource alignedSite.original code.viewOfSource unique code.found
    (code.form.trans code.sourceForm)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {qualification : Facet compiled}

/-- Both ordinary and selected Principal leaves use their original compiler
Source receipt. Equal native function types cannot select an invocation scope. -/
theorem Association.scope_at {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {carrier : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (association : Association qualification headers keys bodyRegistry faults
      mapping world function carrier bindings parameter result) :
    ∃ selected : Staging.Recursive.Scope,
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function selected := by
  cases association with
  | ordinary _ _ code _ support _ _ _ _ _ _ _ =>
    obtain ⟨sidecar, _issued, selected⟩ := code_scope code support.source_receipt support.body.unique
    exact ⟨_, selected⟩
  | principal _ _ code _ support _ _ _ _ _ _ _ =>
    obtain ⟨sidecar, _issued, selected⟩ := code_scope code support.source_receipt support.body.unique
    exact ⟨_, selected⟩

theorem StaticMember.scope_at {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {carrier : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember qualification headers keys bodyRegistry faults
      mapping world function carrier bindings parameter result) :
    ∃ selected : Staging.Recursive.Scope,
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function selected := by
  obtain ⟨association⟩ := member
  exact Association.scope_at association

/-- The selected scope retains the actual original marker and declaration
substitution together with the full local substitution and closure dictionary. -/
theorem StaticMember.original_scope {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {carrier : Value}
    {bindings : List CallableIndexedParameterCertificates.Binding} {parameter result : Ty}
    (member : StaticMember qualification headers keys bodyRegistry faults
      mapping world function carrier bindings parameter result) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar, ∃ active : TypeSystem.Substitution,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan sidecar.caller.key = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar active function) ∧
      (RecursiveStageRegistry.scope sidecar active function).origin.declaration = sidecar.caller.key.declaration ∧
      (RecursiveStageRegistry.scope sidecar active function).origin.declarationSubstitution =
        sidecar.caller.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar active function).origin.localSubstitution = active ∧
      (RecursiveStageRegistry.scope sidecar active function).guards.stages.callerReturnComptime =
        sidecar.caller.function.returnComptime ∧
      (RecursiveStageRegistry.scope sidecar active function).source = function.source ∧
      (RecursiveStageRegistry.scope sidecar active function).context = function.context ∧
      (RecursiveStageRegistry.scope sidecar active function).evidence = function.evidence := by
  obtain ⟨selected, receipt⟩ := StaticMember.scope_at member
  obtain ⟨sidecar, active, issued, same, owner⟩ := RecursiveStageRegistry.Selected.original receipt
  subst selected
  exact ⟨sidecar, active, issued, receipt, owner, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedDirectStageScopeReceipts
