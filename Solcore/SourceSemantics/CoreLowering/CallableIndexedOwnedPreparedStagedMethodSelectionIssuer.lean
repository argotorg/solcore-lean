import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOriginsMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEvidenceMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGenericMethodSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionCoreSupport
import Solcore.SourceSemantics.CoreLowering.CallableMethodResolverTable
import Solcore.SourceSemantics.CoreLowering.CachedMethodEvidenceCoherence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodIssuance

/-! One issuer dispatches the existing empty-method catalog and the validated
full-evidence and actual-origin catalogs. Named and closure collectors share the same proof bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallablePreparedMethodSelection CallablePreparedMethodRuntimeMeaning
open CallableNamedMetadata (environment)

inductive Catalog (compiled : SourceCoreUnifiedCompilation.Compiled) where
  | generic (catalog : CallableIndexedOwnedPreparedStagedGenericMethodSelection.Catalog compiled.sourceProgram)
  | evidence (catalog : CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.Catalog compiled)
  | origins (catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled)

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
    (sourceUnique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type)
    (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodAuthority.Port (compiled := compiled)
      receipt context callerEvidence (RecursiveNamedPreparedStageScopes.registry actualStages)) := by
  cases methods with
  | generic methods =>
      let authentic := CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.authentic receipt actual special
      have support := CallableIndexedOwnedPreparedStagedGenericMethodSelection.selection_support
        authentic checked wellFormed methods selected signatures ledger assumptions sourceUnique unique typed
      exact CallableIndexedOwnedPreparedStagedOperatorMethodIssuance.of_actual receipt actual special
        selected support checked wellFormed catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary actualStages
  | evidence methods =>
      exact CallableIndexedOwnedPreparedStagedEvidenceMethodSelection.of_actual receipt actual special
        selected methods checked wellFormed catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary sourceUnique typed actualStages
  | origins methods =>
      exact CallableIndexedOwnedPreparedStagedOriginsMethodSelection.of_actual receipt actual special
        selected methods checked wellFormed catalog prepared callerMember nodeMember samePlan globals
        signatures ledger assumptions unique dictionary sourceUnique typed actualStages

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionIssuer
