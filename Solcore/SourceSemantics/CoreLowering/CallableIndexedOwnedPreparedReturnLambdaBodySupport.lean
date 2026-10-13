import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts

/-! One original return occurrence retains its exact accepted compiler child.
The static trees carry that child identity and independent Source typing;
application meaning is supplied later by the actual recursive body family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReturnLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal Receipt)

def Syntax (expression : ExpressionId) : TypedSource → ExpressionId → Prop := fun _ id => id = expression

def Child (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) :
    Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ _ _ _ id actual => id = expression ∧ actual = lowered

private theorem finish_injective {type : Ty} {left right : Expr} {fellThrough escaped : Word}
    (same : CompatibleStatements.finish type left fellThrough escaped =
      CompatibleStatements.finish type right fellThrough escaped) : left = right := by
  unfold CompatibleStatements.finish LocalControl.finish LocalLoop.toControl LanguageResult.bind at same
  exact (Expr.caseE.inj (Expr.caseE.inj same).1).1

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

private theorem return_tree
    {source : TypedSource} {context : SourceSemantics.Context} {bodyScope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {statement : StatementId} {node : StatementNode}
    {expression : ExpressionId} {expressionNode : ExpressionNode} {result : TypeSystem.Ty}
    {lowered : SourceCoreBasic.LoweredExpr} {type : Ty}
    (body : statements = [statement])
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) (statementType : node.type = result)
    (read : source.lookupExpression? expression = some expressionNode) (raw : expressionNode.type = result)
    (typed : ExpressionHasType source context expression expressionNode.type)
    (native : lowered.type = type) :
    ∃ tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) source (Syntax expression source)
      (Child expression lowered 0 source) compiled.indexed.layouts.definitions administrative context bodyScope
      (.statements true statements) result type (LocalLoop.returnValue type lowered.expression),
      tree.CatalogSites .reachable registry faults := by
  subst statements
  subst type
  let syntaxTree : GenericLexicalStatements.Syntax source (Syntax expression source) context true [statement] result :=
    .returnValue [] found form statementType read raw typed rfl
  let body : GenericLexicalStatements.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) source (Child expression lowered 0 source)
      context bodyScope true [statement] result lowered.type (LocalLoop.returnValue lowered.type lowered.expression) :=
    .returnValue [] found form read raw ⟨rfl, rfl⟩
  exact ⟨.body syntaxTree body, .body (syntaxTree := syntaxTree) (body := body)⟩

/-- The original callback and one accepted terminal child construct both trees
at the actual Source and parameter context. No child execution law is assumed. -/
theorem of_return_view
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {statement : StatementId} {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
    (body : function.body = [statement])
    (found : function.source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) (statementType : node.type = function.resultType)
    (read : function.source.lookupExpression? expression = some expressionNode)
    (raw : expressionNode.type = function.resultType)
    (typed : ExpressionHasType function.source inputs.context expression expressionNode.type)
    (viewFound : code.view.lookupStatement? statement = some node)
    (viewRead : code.view.lookupExpression? expression = some expressionNode)
    (viewTyped : ExpressionHasType code.view inputs.context expression expressionNode.type) :
    ∃ lowered, ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) (Syntax expression) (Child expression lowered)
      code (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax expression function.source)
        body.context (.statements true function.body) function.resultType := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let children := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics children
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower children) recipe
  have callback : code.lowerBody children = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics children)
  have terminal : Terminal code.view expression function.body := by
    rw [body]
    exact .returning [] viewFound form
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (show policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked from rfl)
    terminal accepted
  have generated := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at generated
  obtain ⟨flow, generated, same⟩ := CompatibleEncoding.bind_ok generated
  have sameFlow : flow = LocalLoop.returnValue code.receipt.resultCore receipt.child.expression :=
    finish_injective ((Except.ok.inj same).trans receipt.emitted)
  subst flow
  obtain ⟨actualTree, actualSites⟩ := return_tree code (registry := registry) (faults := faults)
    (source := code.view) (bodyScope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    body viewFound form statementType viewRead raw viewTyped receipt.sameType
  obtain ⟨tree, sites⟩ := return_tree code (registry := registry) (faults := faults)
    (source := function.source) (bodyScope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    body found form statementType read raw typed receipt.sameType
  let result : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) (Syntax expression) (Child expression receipt.child)
      code (Program.ofChecked compiled.sourceProgram) registry faults := {
    toContext := inputs
    frame := frame
    readFuel := 0
    policy := policy
    callback := callback
    flow := LocalLoop.returnValue code.receipt.resultCore receipt.child.expression
    generated := generated
    projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections code profile).2
    emitted := receipt.emitted
    actualTree := actualTree
    actualSites := actualSites
    tree := tree
    sites := sites
    valid := CallableIndexedLambdaStaticBodySupport.context_valid
      (values := .initial compiled.compatible.checked) code inputs frame sameLedger
    unique := frame.code.graph.nodeOccurrencesUnique }
  refine ⟨receipt.child, result, rfl, ?_⟩
  change GenericImperativeMatch.Syntax function.source (Syntax expression function.source)
    inputs.context (.statements true function.body) function.resultType
  simpa only [body] using (show GenericImperativeMatch.Syntax function.source (Syntax expression function.source)
    inputs.context (.statements true [statement]) function.resultType from
    .body (.returnValue [] found form statementType read raw typed rfl))

/-- Identical Source views retain the original convenience interface. -/
theorem of_return
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (view : code.view = function.source)
    {statement : StatementId} {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
    (body : function.body = [statement])
    (found : function.source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) (statementType : node.type = function.resultType)
    (read : function.source.lookupExpression? expression = some expressionNode)
    (raw : expressionNode.type = function.resultType)
    (typed : ExpressionHasType function.source inputs.context expression expressionNode.type) :
    ∃ lowered, ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) (Syntax expression) (Child expression lowered)
      code (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax expression function.source)
        body.context (.statements true function.body) function.resultType := by
  exact of_return_view code retained inputs frame sameLedger profile body found form statementType read raw typed
    (by simpa only [view] using found) (by simpa only [view] using read) (by simpa only [view] using typed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReturnLambdaBodySupport
