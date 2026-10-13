import Solcore.SourceSemantics.CoreLowering.AcceptedNamedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedFactories
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child Supported)
open AcceptedNamedFactoryAdmission (Produced ReturningAt ExpressionAt)

private theorem returning_typed {source : TypedSource} {control : ControlContext}
    {lexical final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (typed : StatementHasType source control lexical id final facts) :
    ExpressionHasType source lexical expression control.returnType ∧ node.type = control.returnType := by
  have shape : ∀ other, ContainsStatement source id other → other = node := by
    intro other present
    exact Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  cases typed <;> have actual := shape _ (by assumption) <;> cases actual <;> simp_all

private theorem head_typed {source : TypedSource} {control : ControlContext}
    {lexical final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control lexical (id :: rest) final facts) :
    ∃ middle headFacts, StatementHasType source control lexical id middle headFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, head⟩
  | cons head _tail => exact ⟨_, _, head⟩

private theorem lambda_return_type {source : TypedSource} {lexical : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (typed : ExpressionHasType source lexical id node.type)
    (returnFound : source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression)) : returnNode.type = result := by
  generalize sameType : node.type = reported at typed
  cases typed with
  | @intro _ _ actual raw plan contains original rawType rawValid finalValid requirements =>
    have same : actual = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    rw [form] at original
    cases original with
    | lambda _ _ body _ =>
      obtain ⟨_, _, head⟩ := head_typed body
      exact (returning_typed unique returnFound returnForm head).2

private theorem lambda_typed {source : TypedSource} {lexical : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId} {reported : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (typed : ExpressionHasType source lexical id reported) :
    ∃ inner final facts, StatementsHaveType source {returnType := result} inner statements final facts := by
  cases typed with
  | @intro _ _ actual raw plan contains original rawType rawValid finalValid requirements =>
    have same : actual = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    rw [form] at original
    cases original with
    | lambda _ _ body _ => exact ⟨_, _, _, body⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

/-- Full original typing supplies the lambda's declared inner result, independent
of its native representation. -/
theorem return_type {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (certified : SelectedCompilationNamedSourceTyping.Certified header) : returnNode.type = result := by
  obtain ⟨_, _, typed, _complete⟩ := certified.statements
  rw [roots] at typed
  obtain ⟨_, _, first⟩ := head_typed typed
  have lambdaTyped := (returning_typed header.unique outerFound outerForm first).1
  obtain ⟨actual, present, sameType⟩ := lambdaTyped.stored_type
  have same : actual = node := Option.some.inj ((lookupExpression?_complete header.unique present).symm.trans found)
  subst actual
  exact lambda_return_type header.unique found form (sameType ▸ lambdaTyped) returnFound returnForm

/-- The inner typing derivation belongs to the original lambda in this Header. -/
theorem inner_typing {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ inner final facts, StatementsHaveType header.function.source {returnType := result}
      inner statements final facts := by
  obtain ⟨_, _, typed, _complete⟩ := certified.statements
  rw [roots] at typed
  obtain ⟨_, _, first⟩ := head_typed typed
  exact lambda_typed header.unique found form (returning_typed header.unique outerFound outerForm first).1

include aligned in
/-- Original finite return facts identify the produced lambda and inner action.
The compiler supplies the native read, captured scope, allocation and body. -/
theorem produced_of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧ binding.initializer = id)) = none)
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    ∃ produced : Produced prepared header,
      produced.certificate.returnStatement = statement ∧ produced.certificate.returnExpression = expression := by
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      header.function.source id header.function.body := by
    rw [roots]
    exact .returning rest outerFound outerForm
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) terminal aligned.accepted
  let actual : ReturningAt header := ⟨outer, rest, outerNode, id, roots, outerFound, outerForm, receipt⟩
  obtain ⟨fuel, predecessor, root, ⟨head⟩⟩ := AcceptedNamedExpressionFlow.of_header prepared aligned receipt.generated
  let action : ExpressionAt prepared actual := ⟨fuel, predecessor, root, head⟩
  have same : action.head.node = node := Option.some.inj (action.head.found.symm.trans found)
  have actualForm : action.head.node.form = .lambda parameters result [statement] := same ▸ form
  have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy action.root
    (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (reasonAt := header.reasonAt) action.head.found actualForm (same ▸ requirements) (same ▸ coercions) ordinary
  have plain : action.head.special = none := by
    have noSpecial := profile.special
      (Child action.root.selected.policy action.root.selected.lowerBody action.fuel
        (context compiled.indexed prepared.named)) (action.fuel + 1)
    exact Except.ok.inj (action.head.selected.symm.trans noSpecial)
  obtain ⟨reported, read, actualRequirements, actualCoercions, actualOrdinary, ⟨compiler⟩⟩ :=
    AcceptedContextualLambdaReceipt.of_head action.root action.head plain actualForm
  have returnType := return_type roots outerFound outerForm
    action.head.found actualForm returnFound returnForm certified
  let certificate : CallableIndexedOwnedPreparedNamedFactoryAdmission.SourceCertificate
      compiled prepared.named header.function.source header.function.body :=
    ⟨id, terminal, action.head.node, parameters, result, statement, returnNode, expression, reported,
      action.head.found, actualForm, action.head.owner, actualRequirements, actualCoercions, actualOrdinary,
      read, returnFound, returnForm, returnType⟩
  obtain ⟨inner⟩ := AcceptedContextualLambdaReceipt.inner_returning action.root compiler
    (CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal.returning [] returnFound returnForm)
  exact ⟨⟨certificate, actual, action, rfl, rfl, compiler, inner⟩, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedFactories
