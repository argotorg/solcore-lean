import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodRuntimeProfile
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.CallableCoercionPreparation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog

/-! The original coercion selector and final preparation supply the complete
method port. Only syntactic source shape and formation are static inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionIssuance
open Core Frontend SourceInference
open CallablePreparedMethodSelection
open CallableIndexedOwnedPreparedStagedCoercionAuthority
open CallableNamedMetadata (environment)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)

structure Support (selected : CallableCoercionSourceSelection.Certificate
    compiled.sourceProgram caller node available coercion step.method) : Prop where
  formed : CallableCoercionMethodInstantiation.Formation selected.selected.implementation selected.selected.declaration
  range : SourceSemantics.ParameterSubstitution.RangeWellFormed
    (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures) step.method.specialized.parameterSubstitution
  covered : CallableCoercionEvidenceOrigins.CallerCovered caller step.method
  unique : NodeOccurrencesUnique (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram step.method).source
  empty : step.method.specialized.assumptions = []
  parameters : step.method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = [coercion.source]
  result : step.method.specialized.function.inferredBodyType = coercion.target

private theorem exact_member {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact (List.mem_filter.mp member).1

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact of_decide_eq_true (List.mem_filter.mp member).2

private theorem cached_key {method : ExecutableImplMethods.CheckedMethod}
    (cached : Cached compiled method.specialized) : cached.named.signature.key = method.specialized.key := by
  have record := CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook
  exact (exact_key record).symm.trans (congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) cached.same)

private theorem descriptor {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key)) := by
  obtain ⟨origin, selected, _, _⟩ := principal.hook_history
  cases made : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named principal.named.signature.key) with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at made
    split at made
    · next absent => rw [selected] at absent; cases absent
    · cases made
  | ok descriptor => exact ⟨descriptor⟩

include step in
theorem of_actual
    (selected : CallableCoercionSourceSelection.Certificate compiled.sourceProgram caller node available coercion step.method)
    (support : Support step selected)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : Port (compiled := compiled) step context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      SelectedCompilationMethodBodySupport.Certified port.principal port.sourceAt} := by
  have same := CallableCoercionPreparation.step_specialized prepared callerMember nodeMember site resolved step
  have target := step.selected
  rw [same, samePlan] at target
  obtain ⟨initial⟩ := cached_row compiled (exact_member target)
  obtain ⟨diagnostics, code, diagnosticPresent, codeFound, codeAccepted⟩ := NamedCalls.compiled_at compiled.indexed initial.selected
  obtain ⟨generation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed codeAccepted
  let cached : Cached compiled step.method.specialized :=
    ⟨initial.index, initial.named, _, code, initial.selected, initial.same, codeFound, generation⟩
  have chosenTyped := SelectedCompilationMethodSelectionTyping.selects checked bodies cached
    selected.toMethodCertificate support.formed support.range signatures ledger assumptions resolved support.covered step.materialized
  have chosenTyped : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      "Coerce" "coerce" coercion.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram step.method)
      (environment step.dictionary) := by simpa only [dictionary, CoercionStep.requirements] using chosenTyped
  have chosen := chosenTyped.selected
  let principal := CallableIndexedOwnedMethodPrincipal.of_selected cached chosen
  have key : cached.named.signature.key = step.key :=
    (cached_key cached).trans (CallableCoercionPreparation.exact_call_key step.edge).symm
  have member : (cached.named.signature, cached.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = step.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr ?_, ?_⟩
    · rw [globals]
      exact CallableIndexedPreparedInventories.cached_global_at compiled cached.selected
    · simp only [key, decide_true]
  rw [step.global] at member
  have aligned := Prod.mk.inj (List.mem_singleton.mp member)
  obtain ⟨descriptor⟩ := descriptor principal
  obtain ⟨sidecar, _, _, staged⟩ := RecursiveMethodPreparedStageScopes.selected_of_descriptor actualStages principal descriptor
  obtain ⟨retained⟩ := CallableCoercionBodyProvenance.of_accepted checked step.selectedMethod
  obtain ⟨sourceAt⟩ := SelectedCompilationMethodRuntimeProfile.source_at (values := .initial compiled.compatible.checked) cached rfl retained bodies
    chosenTyped support.unique (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm
  have empty : principal.sourceBody.context.assumptions = [] := support.empty
  have emptyDictionary := RecursiveMethodSelectionIdentity.dictionary_empty chosen empty
  let port : Port (compiled := compiled) step context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) := by
    refine ⟨principal, aligned.1, aligned.2, ?_, support.result, chosen, ?_, _, staged,
      ⟨diagnostics, diagnosticPresent, rfl⟩, ?_, sourceAt⟩
    · change cached.named.inputs.map (fun binding => binding.1.scheme.body) = [coercion.source]
      have inputs := CallablePreparedMethodRuntimeProfileFactory.parameters cached
      have types := congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) inputs
      change step.method.specialized.function.typedBody.inputs.map (fun binder => binder.scheme.body) = _ at types
      simpa only [List.map_map, Function.comp_def] using types.symm.trans support.parameters
    · intro body dictionary selectedActual
      exact RecursiveMethodSelectionIdentity.same_empty catalog
        (fun _ _ first second => unique.contains_unique first second) chosen selectedActual empty
    · change CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller compiled.sourceProgram
        cached.named.specialized (environment step.dictionary)
      rw [cached.same]
      exact ⟨[], by rw [support.empty]; rfl, emptyDictionary⟩
  exact ⟨⟨port, SelectedCompilationMethodBodySupport.Certified.of_typed principal sourceAt chosenTyped⟩⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionIssuance
