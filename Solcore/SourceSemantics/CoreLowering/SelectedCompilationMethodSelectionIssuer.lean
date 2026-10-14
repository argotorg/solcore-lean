import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorMethodIssuance

/-! One issuer dispatches the existing empty-method catalog and the validated
full-evidence and actual-origin catalogs. Named and closure collectors share the same proof bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionIssuer
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

open CallableIndexedOwnedPreparedStagedMethodSelectionIssuer (Catalog)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port SelectionSupport)

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

include receipt actual special in
/-- Complete static evidence is recovered from the actual compiler table.
The public body family supplies no method execution or dictionary equality. -/
theorem of_actual
    (selected : OperatorSource actual)
    (methods : Catalog compiled)
        (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
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
    (sourceUnique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty {port : Port (compiled := compiled) receipt context callerEvidence
      (RecursiveNamedPreparedStageScopes.registry actualStages) //
      Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
        port.principal.traitName port.principal.methodName receipt.node.requirements
        port.principal.sourceBody port.principal.dictionary} := by
  obtain ⟨cached⟩ := actual.cached prepared callerMember nodeMember compiled samePlan
  let authentic := SelectedCompilationOperatorMethodIssuance.authentic receipt actual special
  cases methods with
  | generic methods =>
      let chosen := selected.certificate.selected
      have formed := methods.formed _ chosen.implementationMember _ chosen.methodMember
      have emptyAssumptions : actual.selection.method.specialized.assumptions = [] := by
        have fields := CallableCoercionBodyProvenance.specialization_fields chosen.specialized
        rw [fields.2]
        change List.map _ (chosen.implementation.methodAssumptions chosen.trait chosen.declaration) = []
        rw [methods.assumptions chosen.implementation chosen.implementationMember
          chosen.declaration chosen.methodMember chosen.trait chosen.traitMember]
        rfl
      have covered : CallableCoercionEvidenceOrigins.CallerCovered caller actual.selection.method := by
        obtain ⟨headers, resolved, assembled, goals⟩ :=
          CallableCoercionEvidenceOrigins.materialized_operator actual.materialized
        have emptyDictionary : actual.dictionary = [] := List.map_eq_nil_iff.mp (goals.trans emptyAssumptions)
        have allEmpty := assembled.symm.trans emptyDictionary
        have headersEmpty : headers = [] := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp allEmpty).1).1
        rw [headersEmpty] at resolved
        have goalsEmpty : actual.selection.method.traitPredicates = [] := by
          have lengths := resolved.length_eq
          simpa using lengths
        intro goal member
        rw [goalsEmpty] at member
        cases member
      have core := SelectedCompilationOperatorMethodIssuance.selection_core receipt actual special
        selected formed covered checked bodies cached signatures ledger assumptions sourceUnique unique typed
      have support : SelectionSupport authentic selected :=
        ⟨core.formed, core.range, core.covered, core.unique, emptyAssumptions⟩
      exact SelectedCompilationOperatorMethodIssuance.of_actual receipt actual special
        selected support checked bodies catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary actualStages
  | evidence methods =>
      have finalMember : caller ∈ compiled.indexed.base.plan.specializations := samePlan ▸ callerMember
      obtain ⟨evidence⟩ := methods.ready.operator finalMember actual nodeMember
      have formed := methods.formed.formed _ selected.certificate.selected.implementationMember
        _ selected.certificate.selected.methodMember
      have support := SelectedCompilationOperatorMethodIssuance.selection_core receipt actual special
        selected formed evidence.covered checked bodies cached
        signatures ledger assumptions sourceUnique unique typed
      obtain ⟨definition, _member, _identity, instantiated⟩ :=
        selected.certificate.selected.instantiates checked support.formed.parameters support.range
      have coherent := methods.coherent.of_instantiated cached instantiated
      exact SelectedCompilationOperatorMethodIssuance.of_actual_with_evidence receipt actual special
        selected support coherent (evidence.materialized.for_actual actual.materialized)
        checked bodies catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary actualStages
  | origins methods =>
      have finalMember : caller ∈ compiled.indexed.base.plan.specializations := samePlan ▸ callerMember
      obtain ⟨evidence⟩ := methods.ready.operator finalMember actual nodeMember
      have formed := methods.formed.formed _ selected.certificate.selected.implementationMember
        _ selected.certificate.selected.methodMember
      have support := SelectedCompilationOperatorMethodIssuance.selection_core receipt actual special
        selected formed evidence.covered checked bodies cached
        signatures ledger assumptions sourceUnique unique typed
      have coherent := evidence.at_source_receipt selected.toSourceReceipt
      exact SelectedCompilationOperatorMethodIssuance.of_actual_with_origins receipt actual special
        selected support coherent (evidence.materialized.for_actual actual.materialized)
        checked bodies catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodSelectionIssuer
