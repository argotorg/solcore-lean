import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories

/-! The original closure frame and actual BodyWith parameter context construct
per-scope source authority. Genuine captured declarations, coercion exclusions,
program validity and read-fault authority remain explicit. Child grammar,
compiler policy and exact issued-call readiness are separate static obligations.
No body execution or expression meaning law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaOriginalConditions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions OriginalConditionsOn)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {stages : Staging.Recursive.Registry}
  {registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (code : Code compiled.indexed function scope administrative)
  (body : CallableIndexedLambdaStaticBodySupport.BodyWith
    (values := .initial compiled.compatible.checked) expressionSyntax certificates code
    (Program.ofChecked compiled.sourceProgram) registry semanticFaults)

/-- The original parameter installation is shared by every actual selected
scope. Its ledger, covering evidence and node identity come from the same body. -/
theorem at_selected_scope
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (coercions : ∀ id node, Syntax function.source id →
      function.source.lookupExpression? id = some node → node.coercions = [])
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {child : Staging.Recursive.Scope} (selected : stages.Closure function child)
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source body.toContext.context reasonAt current id lowered →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    OriginalConditions compiled code.policy code.compilation readFuel body.toContext.context child
      reasonAt (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      semanticFaults := {
  declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code body.toContext body.frame captured selected
  coercions := by
    simpa only [stages.source selected] using coercions
  sameLedger := body.valid.ledger
  runtimeLedger := body.valid.runtime
  unique := by
    rw [stages.source selected]
    exact body.unique
  wellFormed := wellFormed
  runtime := by
    rw [stages.source selected]
    exact (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
      body.frame body.toContext.extended).1
  covers := by
    rw [stages.evidence selected]
    exact body.valid.covers
  actualFunctionType := by
    rw [code.callables]
    rfl
  uninitialized := uninitialized }

/-- The same admission facts with faults restricted to actual body references. -/
theorem at_selected_scope_on
    (captured : CompatibleExpressionReads.ScopeDeclarations function.source scope function.context)
    (coercions : ∀ id node, Syntax function.source id →
      function.source.lookupExpression? id = some node → node.coercions = [])
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {roots : List NodeId}
    {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {child : Staging.Recursive.Scope} (selected : stages.Closure function child)
    (uninitialized : ∀ current id lowered,
      CompatibleExpressionReads.LoweredRead readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        child.source body.toContext.context reasonAt current id lowered →
      Reaches child.source roots (.expression id) →
      ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) :
    OriginalConditionsOn compiled code.policy code.compilation readFuel body.toContext.context child
      reasonAt (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      roots semanticFaults := {
  declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_selected_scope
    (values := .initial compiled.compatible.checked) code body.toContext body.frame captured selected
  coercions := by
    simpa only [stages.source selected] using coercions
  sameLedger := body.valid.ledger
  runtimeLedger := body.valid.runtime
  unique := by
    rw [stages.source selected]
    exact body.unique
  wellFormed := wellFormed
  runtime := by
    rw [stages.source selected]
    exact (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
      body.frame body.toContext.extended).1
  covers := by
    rw [stages.evidence selected]
    exact body.valid.covers
  actualFunctionType := by
    rw [code.callables]
    rfl
  uninitialized := uninitialized }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLambdaOriginalConditions
