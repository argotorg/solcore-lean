import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport
import Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable
import Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance

/-! Actual final preparation, retained method dictionaries and original Source
parent typing issue methods whose own evidence assumptions may be nonempty. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceMethodSelection
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

structure Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  formed : CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport.Catalog compiled.sourceProgram
  ready : CallableMethodResolverTable.Ready compiled.sourceProgram compiled.indexed.base.plan.specializations
  coherent : CachedMethodEvidenceCoherence.Catalog compiled

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
    (sourceUnique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
      receipt context callerEvidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  have finalMember : caller ∈ compiled.indexed.base.plan.specializations := samePlan ▸ callerMember
  obtain ⟨evidence⟩ := methods.ready.operator finalMember actual nodeMember
  let authentic := CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.authentic receipt actual special
  have support := CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport.selection_support
    authentic checked wellFormed methods.formed selected evidence.covered
    signatures ledger assumptions sourceUnique unique typed
  obtain ⟨cached⟩ := actual.cached prepared callerMember nodeMember compiled samePlan
  obtain ⟨definition, _member, _identity, instantiated⟩ :=
    selected.certificate.selected.instantiates checked support.formed.parameters support.range
  have coherent := methods.coherent.of_instantiated cached instantiated
  exact CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.of_actual_with_evidence receipt actual special
    selected support coherent (evidence.materialized.for_actual actual.materialized)
    checked wellFormed catalog prepared callerMember nodeMember samePlan globals
    signatures ledger assumptions unique dictionary actualStages

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceMethodSelection
