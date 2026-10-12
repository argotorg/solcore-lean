import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPackReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaStaticBodySupport

/-! An empty ordinary lambda body has no child expression obligations. Its
actual retained compiler recipe supplies the loop policy and emitted footer;
its original Source frame and parameter context supply static validity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem empty_tree
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {nativeFrame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {definitions : DataEnvironment} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {result : TypeSystem.Ty} {type : Ty}
    (empty : statements = []) (unit : result = .unit) :
    ∃ tree : GenericImperativeMatch.Tree layouts owner active nativeFrame globals onError values source
      expressionSyntax certificates definitions administrative context scope (.statements true statements)
      result type (LocalLoop.fallthrough type), tree.CatalogSites .reachable registry faults := by
  subst statements
  exact ⟨.body (.nil (.inr unit)) (.nil (.inr unit)),
    .body (syntaxTree := .nil (.inr unit)) (body := .nil (.inr unit))⟩

/-- The two static trees are constructed for the exact compiler view and
original Source. The accepted Code determines the output and footer. -/
theorem of_empty
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (empty : function.body = []) (unit : function.resultType = .unit) :
    ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics expression)
  have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason =
      .ok (LocalLoop.fallthrough code.receipt.resultCore) := by
    exact (congrArg (fun statements => SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      statements code.receipt.resultCore code.reasonAt true code.compilation.internalReason) empty).trans (by simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy])
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  have emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore
      (LocalLoop.fallthrough code.receipt.resultCore) code.compilation.internalReason
      code.compilation.internalReason := Except.ok.inj accepted.symm
  obtain ⟨actualTree, actualSites⟩ : ∃ tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) code.view (expressionSyntax code.view)
      (certificates 0 code.view) compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore
      (LocalLoop.fallthrough code.receipt.resultCore), tree.CatalogSites .reachable registry faults :=
    empty_tree empty unit
  obtain ⟨tree, sites⟩ : ∃ tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) function.source (expressionSyntax function.source)
      (certificates 0 function.source) compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore
      (LocalLoop.fallthrough code.receipt.resultCore), tree.CatalogSites .reachable registry faults :=
    empty_tree empty unit
  exact ⟨{
    toContext := inputs
    frame := frame
    readFuel := 0
    policy := policy
    callback := callback
    flow := LocalLoop.fallthrough code.receipt.resultCore
    generated := generated
    projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections code profile).2
    emitted := emitted
    actualTree := actualTree
    actualSites := actualSites
    tree := tree
    sites := sites
    valid := CallableIndexedLambdaStaticBodySupport.context_valid
      (values := .initial compiled.compatible.checked) code inputs frame sameLedger
    unique := frame.code.graph.nodeOccurrencesUnique }, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
