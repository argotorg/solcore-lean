import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionIssuance
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSourceShapeTable

/-! A finite catalog of closed coercion methods supplies selection support from
original method formation and actual final-plan source shape checks. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedCoercionSelection
open Core Frontend SourceInference
open CallableCoercionMethodInstantiation (Formation bodyInstance)

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  parameters : ∀ implementation, implementation ∈ compiled.sourceProgram.signatures.implementations →
    ∀ method, method ∈ implementation.methods → implementation.parameters = []
  formed : ∀ implementation, implementation ∈ compiled.sourceProgram.signatures.implementations →
    ∀ method, method ∈ implementation.methods → Formation implementation method
  assumptions : ∀ implementation, implementation ∈ compiled.sourceProgram.signatures.implementations →
    ∀ method, method ∈ implementation.methods → ∀ trait, trait ∈ compiled.sourceProgram.signatures.traits →
      implementation.methodAssumptions trait method = []
  shapes : CallableCoercionSourceShapeTable.Ready compiled.sourceProgram compiled.indexed.base.plan.specializations

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

include step in
theorem selection_support {loaded : LoadedProgram}
    (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (catalog : Catalog compiled)
    (selected : CallableCoercionSourceSelection.Certificate compiled.sourceProgram caller node available coercion step.method)
    (callerMember : caller ∈ compiled.indexed.base.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (site : coercion ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available) :
    CallableIndexedOwnedPreparedStagedCoercionIssuance.Support step selected := by
  let chosen := selected.selected
  have formed : Formation chosen.implementation chosen.declaration :=
    catalog.formed chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have domain := chosen.domain
  have parameters := catalog.parameters chosen.implementation chosen.implementationMember chosen.declaration chosen.methodMember
  have substitution : step.method.specialized.parameterSubstitution = [] :=
    List.map_eq_nil_iff.mp (domain.trans parameters)
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      step.method.specialized.parameterSubstitution := by
    intro parameter replacement member
    rw [substitution] at member
    cases member
  have assumptions : step.method.specialized.assumptions = [] := by
    have fields := CallableCoercionBodyProvenance.specialization_fields chosen.specialized
    rw [fields.2]
    change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
    rw [catalog.assumptions chosen.implementation chosen.implementationMember
      chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
    rfl
  have covered : CallableCoercionEvidenceOrigins.CallerCovered caller step.method := by
    obtain ⟨headers, resolved, assembled, goals⟩ := CallableCoercionEvidenceOrigins.materialized step.materialized
    have dictionary : step.dictionary = [] := List.map_eq_nil_iff.mp (goals.trans assumptions)
    have allEmpty := assembled.symm.trans dictionary
    have headersEmpty : headers = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
    rw [headersEmpty] at resolved
    have goalsEmpty : step.method.traitPredicates = [] := by
      have lengths := resolved.length_eq
      simpa using lengths
    intro goal member
    rw [goalsEmpty] at member
    cases member
  obtain ⟨definition, _member, _id, instantiated⟩ := chosen.instantiates checked formed.parameters range
  obtain ⟨types, lexical, facts, typing⟩ := instantiated.certificate wellFormed
  have shape := catalog.shapes.shape callerMember nodeMember site resolved step.selectedMethod
  exact ⟨formed, range, covered, typing.graph_closed.wellFormed.nodeOccurrencesUnique,
    assumptions, shape.parameters, shape.result⟩

include step in
theorem of_actual
    (methods : Catalog compiled)
    {loaded : LoadedProgram}
    (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
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
    (dictionary : callerEvidence = CallableNamedMetadata.environment available)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedCoercionAuthority.Port (compiled := compiled) step context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  obtain ⟨selected⟩ := CallableCoercionSourceSelection.of_accepted step.selectedMethod
  have support := selection_support step checked wellFormed methods selected (samePlan ▸ callerMember) nodeMember site resolved
  exact CallableIndexedOwnedPreparedStagedCoercionIssuance.of_actual step selected support checked wellFormed catalog
    prepared callerMember nodeMember site samePlan globals signatures ledger assumptions resolved unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedClosedCoercionSelection
