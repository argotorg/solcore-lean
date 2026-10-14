import Solcore.SourceSemantics.CoreLowering.AcceptedNamedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyRefinement

/-! The accepted returned lambda retains its full scoped body action. Original
Source typing supplies the inner context; the actual assignment policy refines
the same generated body without changing captured scope or compiler budgets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedScopedLambdaBodyReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedFunctionValues (Header)
open AcceptedNamedFactoryAdmission (ReturningAt ExpressionAt)
open AcceptedNamedBodyFlow (Body)

private theorem returning_typed {source : TypedSource} {control : ControlContext}
    {lexical final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (typed : StatementHasType source control lexical id final facts) :
    ExpressionHasType source lexical expression control.returnType := by
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

/-- The inner typing derivation belongs to the original lambda in this Header. -/
theorem inner_typing {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ inner final facts, StatementsHaveType header.function.source {returnType := result}
      inner statements final facts := by
  obtain ⟨_, _, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  rw [roots] at typed
  obtain ⟨_, _, first⟩ := head_typed typed
  exact lambda_typed header.unique found form (returning_typed header.unique outerFound outerForm first)

/-- The full selected lambda and refined inner body share their actual policy,
parameter allocation, captured scope, root budget and emitted code. -/
structure Produced (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId) where
  actual : ReturningAt header
  action : ExpressionAt prepared actual
  form : action.head.node.form = .lambda parameters result statements
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
    header.function.source actual.expression = .ok (action.head.node, reported)
  requirements : action.head.node.requirements = []
  coercions : action.head.node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (context compiled.indexed prepared.named).owner ∧
      binding.initializer = actual.expression)) = none
  compiler : CallableIndexedLambdaCertificates.Certificate action.root.selected.policy action.root.selected.lowerBody
    action.fuel (context compiled.indexed prepared.named) header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) actual.expression action.head.node
    parameters result statements reported header.reasonAt actual.terminal.child
  inner : Body (AcceptedContextualLambdaReceipt.bodyPolicy action.root action.fuel)
    action.fuel header.function.source compiler.bodyScope statements compiler.resultCore header.reasonAt
    (context compiled.indexed prepared.named).internalReason
    (context compiled.indexed prepared.named).internalReason compiler.body
  ready : inner.tree.Ready

private theorem assignments (actual : ReturningAt header) (action : ExpressionAt prepared actual) :
    CompatibleAssignmentStatements.AssignmentPolicy
      (AcceptedContextualLambdaReceipt.bodyPolicy action.root action.fuel)
      (.initial compiled.compatible.checked)
      (fun site root => prepared.diagnostics.placeReason prepared.named.signature.key site root none)
      (fun site root operator => if operator = .equal then Word.zero
        else prepared.compilation.own.assignments.reasonAt site root (.value operator))
      (fun site root type => prepared.diagnostics.placeReason prepared.named.signature.key site root (some type)) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

private theorem unary (actual : ReturningAt header) (action : ExpressionAt prepared actual) :
    CompatibleBitNotStatements.Policy
      (AcceptedContextualLambdaReceipt.bodyPolicy action.root action.fuel)
      (.initial compiled.compatible.checked)
      (fun site root => prepared.diagnostics.placeReason prepared.named.signature.key site root none)
      (fun site root => prepared.compilation.own.assignments.reasonAt site root .bitNot)
      (fun site root type => prepared.diagnostics.placeReason prepared.named.signature.key site root (some type)) := rfl

private theorem match_policy (actual : ReturningAt header) (action : ExpressionAt prepared actual) :
    CompatibleMatchAmbientLowering.PolicySuccess
      (AcceptedContextualLambdaReceipt.bodyPolicy action.root action.fuel)
      (RecursiveNamedPreparedHeaderPolicies.Prepared.ambientMatch prepared) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend (by rfl)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

include aligned in
/-- Finite original lambda facts select its real accepted branch. No inner body
shape, syntax certificate or execution callback is an input. -/
theorem of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
    {statements : List StatementId}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧ binding.initializer = id)) = none) :
    Nonempty (Produced prepared header parameters result statements) := by
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
  have actualForm : action.head.node.form = .lambda parameters result statements := same ▸ form
  have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy action.root
    (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    (reasonAt := header.reasonAt) action.head.found actualForm (same ▸ requirements) (same ▸ coercions) ordinary
  have plain : action.head.special = none := by
    have noSpecial := profile.special
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child action.root.selected.policy
        action.root.selected.lowerBody action.fuel (context compiled.indexed prepared.named)) (action.fuel + 1)
    exact Except.ok.inj (action.head.selected.symm.trans noSpecial)
  obtain ⟨reported, read, actualRequirements, actualCoercions, actualOrdinary, ⟨compiler⟩⟩ :=
    AcceptedContextualLambdaReceipt.of_head action.root action.head plain actualForm
  have accepted := compiler.bodyCompiled
  rw [AcceptedContextualLambdaReceipt.body_callback action.root action.fuel] at accepted
  obtain ⟨body⟩ := AcceptedNamedBodyFlow.body_of_accepted accepted
  obtain ⟨tree, ready⟩ := body.tree.refine (assignments prepared actual action) (unary prepared actual action)
    (match_policy prepared actual action)
  exact ⟨⟨actual, action, actualForm, reported, read, actualRequirements, actualCoercions,
    actualOrdinary, compiler, ⟨body.flow, tree, body.emitted⟩, ready⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedScopedLambdaBodyReceipts
