import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicSignatureCatalog

/-! Authentic method issuance ties the actual compiler hook to the selected
Source method, full dictionary, real cache slot and staged method scope. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port SelectionSupport)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values source scope id reasonAt lowered)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  (actual : Operator compiled.sourceProgram project caller compilation
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation) (fuel+1)
    source scope id reasonAt policy.callables receipt.node lowered)
  (special : (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation
        (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child policy body fuel compilation)
        (fuel+1) source scope id reasonAt) = .ok (some lowered))

def authentic : Receipt policy body fuel compilation values source scope id reasonAt lowered :=
  ⟨compiled.sourceProgram, project, caller, receipt.node, receipt.metadata, actual, special, receipt.accepted⟩

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

include receipt actual special in
theorem of_actual
    (selected : OperatorSource actual)
    (support : SelectionSupport (authentic receipt actual special) selected)
    {loaded : LoadedProgram}
    (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression receipt.node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (unique : RequirementIdsUnique context)
    (dictionary : callerEvidence = environment actual.available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  let authentic := authentic receipt actual special
  obtain ⟨_, _, _, _, _, target⟩ := actual.prepared prepared callerMember nodeMember
  obtain ⟨initial⟩ := actual.cached prepared callerMember nodeMember compiled samePlan
  obtain ⟨diagnostics, code, diagnosticPresent, codeFound, codeAccepted⟩ := NamedCalls.compiled_at compiled.indexed initial.selected
  obtain ⟨generation⟩ := CallableIndexedNamedGeneration.of_accepted compiled.indexed codeAccepted
  let cached : Cached compiled actual.selection.method.specialized :=
    ⟨initial.index, initial.named, _, code, initial.selected, initial.same, codeFound, generation⟩
  have chosen := selected.toSourceReceipt.selects checked support.formed support.range signatures ledger assumptions support.covered
  have requirements : actual.requirements = receipt.node.requirements := by
    have layout := CallableCallRequirementLayouts.ordinary_owned actual.ordinary
    simpa only [receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm
  have chosen : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      selected.traitName selected.methodName receipt.node.requirements
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram actual.selection.method)
      (environment actual.dictionary) := by
    simpa only [dictionary, requirements] using chosen
  let principal := CallableIndexedOwnedMethodPrincipal.of_selected cached chosen
  have key : cached.named.signature.key = actual.key :=
    (cached_key cached).trans ((congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) target).symm.trans
      (exact_key actual.target.selected))
  have member : (cached.named.signature, cached.index) ∈ compilation.globals.zipIdx.filter
      (fun row => decide (row.1.key = actual.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr ?_, ?_⟩
    · rw [globals]
      exact CallableIndexedPreparedInventories.cached_global_at compiled cached.selected
    · simp only [key, decide_true]
  rw [actual.native.global] at member
  have aligned := Prod.mk.inj (List.mem_singleton.mp member)
  have signature : principal.named.signature = receipt.signature :=
    aligned.1.trans (authentic.signature_eq receipt)
  have slot : principal.cached.index = receipt.index := aligned.2.trans (authentic.index_eq receipt)
  obtain ⟨descriptor⟩ := descriptor principal
  obtain ⟨sidecar, _, _, staged⟩ := RecursiveMethodPreparedStageScopes.selected_of_descriptor actualStages principal descriptor
  obtain ⟨retained⟩ := selected.toSourceReceipt.retained checked
  obtain ⟨sourceAt⟩ := CallablePreparedMethodRuntimeProfileFactory.source_at (values := .initial compiled.compatible.checked) cached rfl retained wellFormed
    chosen support.unique (CallableIndexedOwnedPublicSignatureCatalog.signatures compiled).symm
  refine ⟨⟨authentic, rfl, principal, signature, slot, ?_, chosen, ?_, _, staged, ⟨diagnostics, diagnosticPresent, rfl⟩, sourceAt⟩⟩
  · rcases actual.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
    · exact .inl ⟨operator, operand, form, by simpa only [principal, CallableIndexedOwnedMethodPrincipal.of_selected, form] using selected.dispatch⟩
    · exact .inr ⟨operator, left, right, form, by simpa only [principal, CallableIndexedOwnedMethodPrincipal.of_selected, form] using selected.dispatch⟩
  · intro actualBody actualDictionary selectedActual
    have req : receipt.node.requirements = actual.selection.primaryRequirement :: selected.methodIds :=
      requirements.symm.trans selected.requirements
    rw [req] at chosen selectedActual
    exact RecursiveMethodSelectionIdentity.same_empty catalog
      (fun _ _ first second => unique.contains_unique first second) chosen selectedActual support.empty

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance
