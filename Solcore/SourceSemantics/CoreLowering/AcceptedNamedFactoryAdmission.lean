import Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedFactoryAdmission

/-! The actual named return and lambda compiler actions supply factory admission.
Original Source typing determines the inner return type. The original lambda,
parameter allocation, captured scope and emitted callable remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedFactoryAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal Receipt)
open CallableIndexedOwnedPreparedNamedFactoryAdmission (SourceCertificate Certificate)
open CallableIndexedNamedGeneration (context)
open AcceptedNamedExpressionFlow (Head specialAction)

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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) : returnNode.type = result := by
  obtain ⟨_, _, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  rw [roots] at typed
  obtain ⟨_, _, first⟩ := head_typed typed
  have lambdaTyped := (returning_typed header.unique outerFound outerForm first).1
  obtain ⟨actual, present, sameType⟩ := lambdaTyped.stored_type
  have same : actual = node := Option.some.inj ((lookupExpression?_complete header.unique present).symm.trans found)
  subst actual
  exact lambda_return_type header.unique found form (sameType ▸ lambdaTyped) returnFound returnForm

/-- The original return head and its exact accepted child action. -/
structure ReturningAt (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  statement : StatementId
  rest : List StatementId
  node : StatementNode
  expression : ExpressionId
  roots : header.function.body = statement :: rest
  found : header.function.source.lookupStatement? statement = some node
  form : node.form = .returnStmt (some expression)
  terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body

/-- This retains the real predecessor budget and complete selected compiler policy. -/
structure ExpressionAt (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (actual : ReturningAt header) where
  fuel : Nat
  predecessor : actual.terminal.childFuel = fuel + 1
  root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := compiled) prepared.named prepared.diagnostics prepared.code prepared.compilation
    fuel header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    actual.expression header.reasonAt actual.terminal.child
  head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed prepared.named)
    header.function.source (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    actual.expression header.reasonAt actual.terminal.child

/-- The source certificate and full literal lambda compilation belong to the
same return child, including parameter allocation, body and production hooks. -/
structure Produced (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  certificate : SourceCertificate compiled prepared.named header.function.source header.function.body
  actual : ReturningAt header
  action : ExpressionAt prepared actual
  expression : certificate.expression = actual.expression
  node : certificate.node = action.head.node
  compiler : CallableIndexedLambdaCertificates.Certificate action.root.selected.policy action.root.selected.lowerBody
    action.fuel (context compiled.indexed prepared.named) header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) actual.expression action.head.node
    certificate.parameters certificate.result [certificate.returnStatement] certificate.reported header.reasonAt
    actual.terminal.child
  inner : Receipt (AcceptedContextualLambdaReceipt.bodyPolicy action.root action.fuel)
    action.fuel header.function.source compiler.bodyScope certificate.returnExpression
    [certificate.returnStatement] compiler.resultCore header.reasonAt
    (context compiled.indexed prepared.named).internalReason
    (context compiled.indexed prepared.named).internalReason compiler.body

/-- Alternatives retain either the whole accepted body or its exact return,
selected policy and expression action. No broad unsupported flag is introduced. -/
inductive Unsupported (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | outer (actual : AcceptedNamedBodyAdmission.BodyAt header)
      (shape : ¬ ∃ statement rest node expression,
        header.function.body = statement :: rest ∧
        header.function.source.lookupStatement? statement = some node ∧
        node.form = .returnStmt (some expression))
  | expression (actual : ReturningAt header) (action : ExpressionAt prepared actual)
      (shape : ¬ ∃ parameters result statements,
        action.head.node.form = .lambda parameters result statements)
  | special (actual : ReturningAt header) (action : ExpressionAt prepared actual)
      (lowered : SourceCoreBasic.LoweredExpr) (selected : action.head.special = some lowered)
  | body (actual : ReturningAt header) (action : ExpressionAt prepared actual)
      (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId)
      (form : action.head.node.form = .lambda parameters result statements)
      (reported : Core.Ty)
      (compiler : CallableIndexedLambdaCertificates.Certificate action.root.selected.policy action.root.selected.lowerBody
        action.fuel (context compiled.indexed prepared.named) header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) actual.expression action.head.node
        parameters result statements reported header.reasonAt actual.terminal.child)
      (shape : ¬ ∃ statement node expression, statements = [statement] ∧
        header.function.source.lookupStatement? statement = some node ∧
        node.form = .returnStmt (some expression))

include aligned in
private theorem returning_at
    {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode} {id : ExpressionId}
    (roots : header.function.body = outer :: rest)
    (found : header.function.source.lookupStatement? outer = some outerNode)
    (form : outerNode.form = .returnStmt (some id)) : Nonempty (ReturningAt header) := by
  have terminal : Terminal header.function.source id header.function.body := by
    rw [roots]
    exact .returning rest found form
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) terminal aligned.accepted
  exact ⟨⟨outer, rest, outerNode, id, roots, found, form, receipt⟩⟩

include aligned in
private theorem expression_at (actual : ReturningAt header) : Nonempty (ExpressionAt prepared actual) := by
  obtain ⟨fuel, predecessor, root, ⟨head⟩⟩ :=
    AcceptedNamedExpressionFlow.of_header prepared aligned actual.terminal.generated
  exact ⟨⟨fuel, predecessor, root, head⟩⟩

private theorem produce (actual : ReturningAt header) (action : ExpressionAt prepared actual)
    {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (plain : action.head.special = none)
    (form : action.head.node.form = .lambda parameters result [statement])
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (Produced prepared header) := by
  obtain ⟨reported, read, requirements, coercions, ordinary, ⟨compiler⟩⟩ :=
    AcceptedContextualLambdaReceipt.of_head action.root action.head plain form
  have returnType := return_type actual.roots actual.found actual.form action.head.found form
    returnFound returnForm wellFormed
  let certificate : SourceCertificate compiled prepared.named header.function.source header.function.body :=
    ⟨actual.expression, actual.terminal.terminal, action.head.node, parameters, result,
      statement, returnNode, expression, reported, action.head.found, form, action.head.owner,
      requirements, coercions, ordinary, read, returnFound, returnForm, returnType⟩
  obtain ⟨inner⟩ := AcceptedContextualLambdaReceipt.inner_returning action.root compiler
    (CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal.returning [] returnFound returnForm)
  exact ⟨⟨certificate, actual, action, rfl, rfl, compiler, inner⟩⟩

include aligned in
/-- The accepted Header is classified without evaluating another source scanner.
Only the ordinary singleton-return lambda lane produces a factory certificate. -/
theorem of_header (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (Produced prepared header) ∨ Nonempty (Unsupported prepared header) := by
  classical
  obtain ⟨body⟩ := AcceptedNamedBodyFlow.body_of_accepted aligned.accepted
  by_cases shape : ∃ statement rest node expression, header.function.body = statement :: rest ∧
      header.function.source.lookupStatement? statement = some node ∧ node.form = .returnStmt (some expression)
  · obtain ⟨statement, rest, node, expression, roots, found, form⟩ := shape
    obtain ⟨actual⟩ := returning_at prepared aligned roots found form
    obtain ⟨action⟩ := expression_at prepared aligned actual
    by_cases lambdaForm : ∃ parameters result statements,
        action.head.node.form = .lambda parameters result statements
    · obtain ⟨parameters, result, statements, actualForm⟩ := lambdaForm
      cases selected : action.head.special with
      | some lowered => exact .inr ⟨.special actual action lowered selected⟩
      | none =>
        obtain ⟨reported, _read, _requirements, _coercions, _ordinary, ⟨compiler⟩⟩ :=
          AcceptedContextualLambdaReceipt.of_head action.root action.head selected actualForm
        by_cases inner : ∃ statement node expression, statements = [statement] ∧
            header.function.source.lookupStatement? statement = some node ∧ node.form = .returnStmt (some expression)
        · obtain ⟨statement, node, expression, statementsEq, found, form⟩ := inner
          subst statements
          exact .inl (produce prepared actual action selected actualForm found form wellFormed)
        · exact .inr ⟨.body actual action parameters result statements actualForm reported compiler inner⟩
    · exact .inr ⟨.expression actual action lambdaForm⟩
  · exact .inr ⟨.outer body shape⟩

include aligned in
/-- Original finite shape and special-gate facts discharge the narrow branch.
The compiler derives owner, native read, allocation, body and hooks. -/
theorem of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCertificate compiled prepared.named header.function.source header.function.body) := by
  have terminal : Terminal header.function.source id header.function.body := by
    rw [roots]
    exact .returning rest outerFound outerForm
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) terminal aligned.accepted
  let actual : ReturningAt header := ⟨outer, rest, outerNode, id, roots, outerFound, outerForm, receipt⟩
  obtain ⟨action⟩ := expression_at prepared aligned actual
  have same : action.head.node = node := Option.some.inj (action.head.found.symm.trans found)
  have actualForm : action.head.node.form = .lambda parameters result [statement] := same ▸ form
  have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy action.root
    (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (reasonAt := header.reasonAt) action.head.found actualForm (same ▸ requirements) (same ▸ coercions) ordinary
  have plain : action.head.special = none := by
    have noSpecial := profile.special
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child action.root.selected.policy action.root.selected.lowerBody
        action.fuel (context compiled.indexed prepared.named)) (action.fuel + 1)
    exact Except.ok.inj (action.head.selected.symm.trans noSpecial)
  obtain ⟨produced⟩ := produce prepared actual action plain actualForm returnFound returnForm wellFormed
  exact ⟨produced.certificate⟩

include aligned in
/-- Reverse transport retains the exact cache identity and compiled roots. -/
theorem source_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (certificate : SourceCertificate compiled prepared.named header.function.source header.function.body) :
    Nonempty (Certificate compiled named) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  obtain ⟨source, body, _result⟩ :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned
  rw [source, body, namedEq] at certificate
  exact ⟨certificate⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedFactoryAdmission
