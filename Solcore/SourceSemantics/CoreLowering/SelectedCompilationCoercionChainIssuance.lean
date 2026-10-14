import Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationClosedCoercionSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain

/-! Original Source path typing and accepted compiler steps produce the ordered
method chain. Every method port is issued from the same final preparation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionChainIssuance
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedCoercionChain (Chain)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (bodies : SelectedCompilationBodyTyping.Bodies compiled)
  (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
  (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
    preparationFuel budget = .ok compilation.plan)
  (callerMember : caller ∈ compilation.plan.specializations)
  (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
  (samePlan : compilation.plan = compiled.indexed.base.plan)
  (globals : compilation.globals = compiled.indexed.base.globals)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (signatures : context.signatures = compiled.sourceProgram.signatures)
  (ledger : context.solvedRequirements = caller.function.solvedRequirements)
  (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
  (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.sourceProgram caller.key caller.assumptions = .ok available)
  (unique : RequirementIdsUnique context)
  (dictionary : invocation.evidence = CallableNamedMetadata.environment available)
  (actualStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

def Certified {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
    {steps : List CoercionStep} {calls : List CallableCoercionSpine.Call}
    (chain : Chain compiled project compilation caller available scope node policy context invocation
      (RecursiveNamedPreparedStageScopes.registry actualStages) source target input steps output calls) : Prop :=
  match chain with
  | .nil => True
  | .cons _ port _ tail =>
      SelectedCompilationMethodBodySupport.Certified port.principal port.sourceAt ∧ Certified tail

include methods checked bodies catalog prepared callerMember nodeMember samePlan globals
  signatures ledger assumptions resolved unique dictionary actualStages in
theorem of_spine {input output : SourceCoreBasic.LoweredExpr} {steps : List CoercionStep}
    {calls : List CallableCoercionSpine.Call}
    (spine : CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available
      scope node policy input steps output calls)
    {source target : TypeSystem.Ty} (valid : CoercionPathValid context source target steps)
    (sites : ∀ step ∈ steps, step ∈ node.coercions ++ CallableCoercionPreparation.argumentSteps node) :
    Nonempty {chain : Chain compiled project compilation caller available scope node policy context invocation
      (RecursiveNamedPreparedStageScopes.registry actualStages) source target input steps output calls // Certified actualStages chain} := by
  induction spine generalizing source with
  | nil => cases valid; exact ⟨⟨.nil, True.intro⟩⟩
  | @cons input step middle rest output call calls head tail ih =>
    cases valid with
    | cons valid remaining =>
      obtain ⟨⟨port, certified⟩⟩ := SelectedCompilationClosedCoercionSelection.of_actual head methods checked
        bodies catalog prepared callerMember nodeMember (sites step (by simp)) samePlan globals
        signatures ledger assumptions resolved unique dictionary actualStages
      obtain ⟨⟨chain, tailCertified⟩⟩ := ih remaining (fun step member => sites step (List.mem_cons_of_mem _ member))
      exact ⟨⟨.cons head port valid chain, certified, tailCertified⟩⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionChainIssuance
