import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedLambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.CompilerProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedExpressions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedClosureAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReachedFormation
import Solcore.SourceSemantics.CoreLowering.AcceptedTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.ReadBundles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCachedInputs
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
import Solcore.Frontend.ResidualLexicalScopes
import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.SourceSpecializationLocalLexicalSubstitutionChildren

/-!
# Accepted programs and contextual lambdas

Completion of a program's bodies, roots, closures and methods, and the receipts of contextual lambdas and generalized initializers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaReceipt
/-! An ordinary lambda action supplies the actual reader, original empty metadata,
initializer exclusion and full parameter/body/allocation/hook compiler receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open AcceptedNamedExpressionFlow (Head specialAction)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {parameters : List TypedBinder}
  {result : TypeSystem.Ty} {statements : List StatementId} {lowered : SourceCoreBasic.LoweredExpr}

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem initializer_none
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .lambda parameters result statements) :
    compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none := by
  have accepted := head.selected
  rw [plain] at accepted
  unfold specialAction at accepted
  rw [root.compilerPolicy.lowerSpecial] at accepted
  have sameSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals
      (context compiled.indexed named).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, head.found, form]
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special at accepted
  simp only [sameSource, bind, Except.bind, head.found, pure, Except.pure] at accepted
  cases selected : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) with
  | none => rfl
  | some binding =>
    simp only [selected, Option.filter_some, ne_eq, reduceCtorEq, not_false_eq_true, decide_true,
      ↓reduceIte] at accepted
    obtain ⟨actual, _binding, accepted⟩ := bind_ok accepted
    obtain ⟨result, _initializer, accepted⟩ := bind_ok accepted
    cases accepted

private theorem ordinary_metadata
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .lambda parameters result statements) :
    ∃ type, root.selected.policy.readExpression source id = .ok (head.node, type) ∧
      CompatibleExpressionReads.Metadata compiled.compatible.checked source id head.node type := by
  have sameSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals
      (context compiled.indexed named).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, head.found, form]
  have readPolicy : root.selected.policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
    rw [root.compilerPolicy.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  have accepted := head.accepted
  have selected := head.selected
  rw [plain] at selected
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [head.owner, ne_eq, not_true_eq_false, ↓reduceIte, head.found,
    bind, Except.bind, pure, Except.pure] at accepted
  cases hook : root.selected.policy.lowerSpecial? <;>
    simp only [specialAction, hook] at selected accepted
  all_goals try rw [selected] at accepted
  all_goals
    simp only [form] at accepted
    obtain ⟨pair, read, accepted⟩ := bind_ok accepted
    obtain ⟨node, type⟩ := pair
    have actual := CompatibleExpressionReads.metadata_of_read (readPolicy ▸ read)
    have same := Option.some.inj (actual.found.symm.trans head.found)
    subst node
    exact ⟨type, read, actual⟩

/-- The full original lambda compilation belongs to this same accepted action. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .lambda parameters result statements) :
    ∃ reported,
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id =
        .ok (head.node, reported) ∧
      head.node.requirements = [] ∧ head.node.coercions = [] ∧
      compiled.indexed.base.locals.bindings.find? (fun binding =>
        decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none ∧
      Nonempty (CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody
        fuel (context compiled.indexed named) source scope id head.node parameters result statements
        reported reasonAt lowered) := by
  have ordinary := initializer_none root head plain form
  obtain ⟨reported, read, actual⟩ := ordinary_metadata root head plain form
  have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.lambda_policy root
    (scope := scope) (reasonAt := reasonAt)
    head.found form actual.requirements actual.coercions ordinary
  refine ⟨reported, profile.read ▸ read, actual.requirements, actual.coercions, ordinary, ?_⟩
  apply CallableIndexedLambdaCertificates.of_accepted _ head.owner head.found read form head.accepted
  change specialAction root.selected.policy root.selected.lowerBody fuel
    (context compiled.indexed named) source scope id reasonAt = .ok none
  exact plain ▸ head.selected

/-- The inner statement callback uses the same literal policy and minimum child
budget retained by the accepted lambda action. -/
def bodyPolicy (budget : Nat) : SourceCoreLoops.Policy :=
  let representation := (CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key []
  {representation.loopsWithSourceCells representation.expressions.sourceCells
    (context compiled.indexed named).solvedRequirements compilation.own.assignments diagnostics
    (context compiled.indexed named).owner
    (FunctionCode.children root.selected.policy root.selected.lowerBody budget (context compiled.indexed named)) with
    sourceCells := representation.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation compiled.indexed.base.locals named.signature.key []}

/-- The lambda receipt's body equation is the genuine statement compiler action. -/
theorem body_callback (budget : Nat) :
    root.selected.lowerBody
      (FunctionCode.children root.selected.policy root.selected.lowerBody budget (context compiled.indexed named)) =
      SourceCoreLoops.lowerStatementsWithPolicy (bodyPolicy root budget) := by
  dsimp only [bodyPolicy]
  rw [root.selected.recipe]
  rfl

/-- A returning inner body exposes its actual generated child and emitted
footer from the full lambda receipt, without a second body or expression scan. -/
theorem inner_returning {node : ExpressionNode} {reported : Core.Ty}
    (compiler : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody
      fuel (context compiled.indexed named) source scope id node parameters result statements
      reported reasonAt lowered)
    {expression : ExpressionId}
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal source expression statements) :
    Nonempty (CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt
      (bodyPolicy root fuel) fuel source compiler.bodyScope expression statements compiler.resultCore reasonAt
      (context compiled.indexed named).internalReason (context compiled.indexed named).internalReason compiler.body) := by
  have accepted := compiler.bodyCompiled
  rw [body_callback root fuel] at accepted
  exact CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted rfl terminal accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedFactoryAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedScopedLambdaBodyReceipts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedScopedFactoryAdmission
/-! Flat original profiles close the actual scoped lambda body and its ordered
expression actions. The same derived scan issues both formation and closure
certificates without a caller-provided grammar or body completion premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedScopedFactoryAdmission
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open AcceptedScopedLambdaBodyReceipts (Produced)
open CallableIndexedOwnedPreparedScopedFactoryAdmission (SourceCertificate Certificate)
open CallableIndexedOwnedPreparedScopedClosureAdmission (SourceBodyCertificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {directRows : List SourceSpecialization.SpecializedFunction} {directOnly allowIndices allowConstructors : Bool}

/-- Every expression proof comes from an actual child compiler action at its
minimum root budget and original lexical scope. -/
theorem Produced.scan (produced : Produced prepared header parameters result statements)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ScopedSourceBodyAdmission.Scan header.function.source
      (fun id => GeneralSyntax header.function.source id (DirectSite directRows)) result true statements := by
  have readPolicy : (AcceptedContextualLambdaReceipt.bodyPolicy produced.action.root produced.action.fuel).readStatement =
      SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := rfl
  obtain ⟨closed, monomorphic, members⟩ := bodyProfile.facts produced.inner.tree readPolicy produced.ready
  have children : ∀ child ∈ produced.inner.tree.children,
      GeneralSyntax header.function.source child.expression (DirectSite directRows) := by
    intro child member
    obtain ⟨trace⟩ := AcceptedNamedExpressionFlow.Trace.of_accepted
      (root := produced.action.root) expressions.metadata supported expressions.covered child.accepted
    cases trace.syntax_or_boundary expressions.covered with
    | inl grammar => exact grammar
    | inr residual =>
      obtain ⟨boundary⟩ := residual
      exact False.elim (boundary.impossible_ordinary expressions.metadata expressions.compositeForms expressions.noInitializer
        expressions.ordinaryArguments expressions.ordinaryMetadata expressions.indexOperands expressions.constructorRanges (members child member))
  obtain ⟨inner, final, facts, typed⟩ := AcceptedScopedLambdaBodyReceipts.inner_typing
    produced.actual.roots produced.actual.found produced.actual.form produced.action.head.found produced.form wellFormed
  obtain ⟨_facts, certified⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certified.local_identity_ownership
  have binders := AcceptedNamedBodyBindings.of_monomorphic produced.inner.tree readPolicy
    header.unique ownership typed monomorphic
  exact produced.inner.tree.scan_complete readPolicy closed header.unique ownership children binders typed

private theorem origin_owner : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
    prepared.named.specialized.function.typedBody.owner = signature.id := by
  obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, ?_⟩
  rw [prepared.same, fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner,
    identities.2.1, identities.1]

include aligned in
/-- Formation and later body admission share the same derived original scan. -/
theorem of_produced (produced : Produced prepared header parameters result statements)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (bareUnary : PreparedBranchingBareUnarySyntax.Body header.function.source statements)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCertificate compiled prepared.named header.function.source header.function.body) ∧
      Nonempty (SourceBodyCertificate compiled prepared.named directRows statements) := by
  have scan := Produced.scan prepared produced expressions bodyProfile supported wellFormed
  let factory : SourceCertificate compiled prepared.named header.function.source header.function.body := {
    expression := produced.actual.expression
    terminal := produced.actual.terminal.terminal
    node := produced.action.head.node
    parameters := parameters
    result := result
    statements := statements
    reported := produced.reported
    found := produced.action.head.found
    form := produced.form
    owner := produced.action.head.owner
    requirements := produced.requirements
    coercions := produced.coercions
    ordinary := produced.ordinary
    read := produced.read
    scan := scan.map (fun _ _ => True.intro)
    bareUnary := bareUnary }
  obtain ⟨signature, member, owner⟩ := origin_owner prepared
  have source := (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned).1
  have typedScan := scan
  have metadata := expressions.metadata
  rw [source] at typedScan metadata
  exact ⟨⟨factory⟩, ⟨⟨result, typedScan, metadata, signature, member, owner⟩⟩⟩

include aligned in
/-- The accepted outer return identifies the literal lambda. Its actual scoped
body and expression receipts derive both certificate lanes internally. -/
theorem of_returning {outer : StatementId} {rest : List StatementId} {outerNode : StatementNode}
    {id : ExpressionId} {node : ExpressionNode}
    (roots : header.function.body = outer :: rest)
    (outerFound : header.function.source.lookupStatement? outer = some outerNode)
    (outerForm : outerNode.form = .returnStmt (some id))
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧ binding.initializer = id)) = none)
    (expressions : AcceptedCompilerExpressionProfile.Profile compiled.indexed prepared.named
      header.function.source directRows directOnly allowIndices allowConstructors)
    (bodyProfile : AcceptedCompilerBodySubsetProfile.Profile header.function.source expressions.ids statements result)
    (bareUnary : PreparedBranchingBareUnarySyntax.Body header.function.source statements)
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCertificate compiled prepared.named header.function.source header.function.body) ∧
      Nonempty (SourceBodyCertificate compiled prepared.named directRows statements) := by
  obtain ⟨produced⟩ := AcceptedScopedLambdaBodyReceipts.of_returning prepared aligned roots outerFound outerForm
    found form requirements coercions ordinary
  exact of_produced prepared aligned produced expressions bodyProfile bareUnary supported wellFormed

include aligned in
/-- Full cache identity transports the factory certificate to its original row. -/
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

/-- Full cache identity transports the inner certificate without replacing its source. -/
theorem closure_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (certificate : SourceBodyCertificate compiled prepared.named directRows statements) :
    Nonempty (SourceBodyCertificate compiled named directRows statements) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  rw [namedEq] at certificate
  exact ⟨certificate⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedScopedFactoryAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedClosureAdmission
/-! The actual returned lambda retains its inner expression compiler action.
That same action supplies the ordinary closure certificate; no separate body
or expression traversal is evaluated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedClosureAdmission
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported Child)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedClosureAdmission (OrdinaryBodyCertificate)
open AcceptedNamedFactoryAdmission (Produced ReturningAt ExpressionAt)
open AcceptedNamedExpressionFlow (Trace Boundary ReachedForms ReachedArguments)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {directRows : List SourceSpecialization.SpecializedFunction}

/-- The minimum budget and captured scope are those in the same lambda action. -/
theorem Produced.trace (produced : Produced prepared header)
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation) :
    Nonempty (Trace produced.action.root header.function.source produced.compiler.bodyScope header.reasonAt
      (min produced.inner.childFuel produced.action.fuel) produced.certificate.returnExpression produced.inner.child) := by
  apply Trace.of_accepted metadata supported covered
  exact produced.inner.generated

private theorem origin_owner : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
    prepared.named.specialized.function.typedBody.owner = signature.id := by
  obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, ?_⟩
  rw [prepared.same, fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner,
    identities.2.1, identities.1]

/-- A remaining boundary records the actual inner trace and its exact path. -/
structure Unsupported (produced : Produced prepared header)
    (directRows : List SourceSpecialization.SpecializedFunction) where
  trace : Trace produced.action.root header.function.source produced.compiler.bodyScope header.reasonAt
    (min produced.inner.childFuel produced.action.fuel) produced.certificate.returnExpression produced.inner.child
  boundary : Boundary trace

include aligned in
/-- The compiler traversal supplies syntax or the indexed unexpanded action. -/
theorem of_produced_or_boundary (produced : Produced prepared header)
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation) :
    Nonempty (OrdinaryBodyCertificate compiled prepared.named directRows [produced.certificate.returnStatement]) ∨
      Nonempty (Unsupported prepared produced directRows) := by
  obtain ⟨trace⟩ := Produced.trace prepared produced metadata supported covered
  cases trace.syntax_or_boundary covered with
  | inl grammar =>
    obtain ⟨signature, member, owner⟩ := origin_owner prepared
    have terminal := produced.inner.terminal
    have source := (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned).1
    have actualGrammar := Eq.mp (congrArg (fun source =>
      GeneralSyntax source produced.certificate.returnExpression (DirectSite directRows)) source) grammar
    have actualTerminal := Eq.mp (congrArg (fun source =>
      CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal source
        produced.certificate.returnExpression [produced.certificate.returnStatement]) source) terminal
    rw [source] at metadata
    exact .inl ⟨⟨produced.certificate.returnExpression, actualTerminal, actualGrammar,
      metadata, signature, member, owner⟩⟩
  | inr residual =>
    obtain ⟨boundary⟩ := residual
    exact .inr ⟨⟨trace, boundary⟩⟩

include aligned in
/-- Finite original direct/read reachability closes only the actual inner path. -/
theorem of_produced (produced : Produced prepared header)
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    {reached : ExpressionId → Prop}
    (forms : ReachedForms header.function.source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments header.function.source reached)
    (present : reached produced.certificate.returnExpression) :
    Nonempty (OrdinaryBodyCertificate compiled prepared.named directRows [produced.certificate.returnStatement]) := by
  cases of_produced_or_boundary prepared aligned produced metadata supported covered with
  | inl result => exact result
  | inr residual =>
    obtain ⟨residual⟩ := residual
    exact False.elim (residual.boundary.impossible metadata forms initializers arguments present)

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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
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
  have returnType := AcceptedNamedFactoryAdmission.return_type roots outerFound outerForm
    action.head.found actualForm returnFound returnForm wellFormed
  let certificate : CallableIndexedOwnedPreparedNamedFactoryAdmission.SourceCertificate
      compiled prepared.named header.function.source header.function.body :=
    ⟨id, terminal, action.head.node, parameters, result, statement, returnNode, expression, reported,
      action.head.found, actualForm, action.head.owner, actualRequirements, actualCoercions, actualOrdinary,
      read, returnFound, returnForm, returnType⟩
  obtain ⟨inner⟩ := AcceptedContextualLambdaReceipt.inner_returning action.root compiler
    (CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal.returning [] returnFound returnForm)
  exact ⟨⟨certificate, actual, action, rfl, rfl, compiler, inner⟩, rfl, rfl⟩

include aligned in
/-- The same accepted inner body closes its direct/read certificate. Original
typing supplies its declared result; reached facts close actual trace boundaries. -/
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
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    {reached : ExpressionId → Prop}
    (forms : ReachedForms header.function.source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments header.function.source reached)
    (present : reached expression) :
    Nonempty (OrdinaryBodyCertificate compiled prepared.named directRows [statement]) := by
  obtain ⟨produced, statementEq, expressionEq⟩ := produced_of_returning prepared aligned roots outerFound outerForm
    found form requirements coercions ordinary returnFound returnForm wellFormed
  have reachedInner : reached produced.certificate.returnExpression := expressionEq ▸ present
  have result := of_produced prepared aligned produced metadata supported covered forms initializers arguments reachedInner
  simpa only [statementEq] using result

/-- Full cache identity transports the closure certificate without replacing its source. -/
theorem source_of_header {index : Nat} {named : SourceCoreGeneralFunctions.Function} {body : List StatementId}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row)
    (certificate : OrdinaryBodyCertificate compiled prepared.named directRows body) :
    Nonempty (OrdinaryBodyCertificate compiled named directRows body) := by
  have namedEq := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named prepared selected same
  rw [namedEq] at certificate
  exact ⟨certificate⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedClosureAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedRefinedBodyAdmission
/-! One refined accepted body supplies all actual expression actions. Closed
structure and original monomorphic bindings discharge the body boundary;
every remaining expression residual refers to a child of this same receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedRefinedBodyAdmission
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedBodyAdmission (BodyAt)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)

theorem of_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (receipt : BodyAt header)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite directRows instantiation)
    (closed : receipt.tree.closed = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = [])
    (excluded : ∀ child ∈ receipt.tree.children,
      ¬ Nonempty (AcceptedNamedExpressionFlow.Residual prepared header (DirectSite directRows)
        child.fuel header.function.source child.scope child.expression child.lowered))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows := by
  have children : ∀ child ∈ receipt.tree.children,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        header.function.source child.expression (DirectSite directRows) := by
    intro child member
    cases AcceptedNamedExpressionFlow.syntax_of_header prepared aligned metadata supported covered child.accepted with
    | inl grammar => exact grammar
    | inr residual => exact False.elim (excluded child member residual)
  cases AcceptedNamedBodyBindings.of_header prepared aligned wellFormed receipt.tree with
  | inl bindings =>
    obtain ⟨final, facts, typed, _⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
    exact ⟨metadata, receipt.tree.scan
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
      closed header.unique (by
        obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
        rw [header.frame.source]
        exact certificate.local_identity_ownership) children bindings typed⟩
  | inr generalized =>
    obtain ⟨binding, member, different⟩ := generalized
    exact False.elim (different (monomorphic binding member))

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedRefinedBodyAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedContextualGeneralizedInitializerReceipt
/-! An actual named compiler head either has no initializer override or retains
its ordered generalized bundle. The original callback supplies every instance
receipt, without a separate syntax scan or an assumed initializer selection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualGeneralizedInitializerReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes
open GeneralizedLocalInitializerCompilation (Receipt namedInputs)
open AcceptedNamedExpressionFlow (Head)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) : ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

/-- The selected initializer branch is independent of the original node form.
Its contextual source read and every candidate emission are actual accepted calls. -/
theorem of_special_output {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : Prepared checked} {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compilation : Compilation prepared named diagnostics code)
    {rootFuel budget : Nat} {current : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {initial : SourceCoreLocalPolymorphism.Binding} {output : Option SourceCoreBasic.LoweredExpr}
    (selected : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)) = some initial)
    (accepted : special compilation rootFuel current child budget source scope id reasonAt = .ok output) :
    ∃ binding lowered, output = some lowered ∧
      prepared.base.locals.binding current.owner initial.binder.id = .ok binding ∧
      Nonempty (Receipt (namedInputs compilation rootFuel budget current scope id reasonAt) binding [] lowered) := by
  unfold special at accepted
  obtain ⟨viewed, _, accepted⟩ := bind_ok accepted
  cases found : viewed.lookupExpression? id with
  | none => simp [found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  | some node =>
    simp only [found, bind, Except.bind, pure, Except.pure] at accepted
    simp only [selected, Option.filter_some, ne_eq, reduceCtorEq, not_false_eq_true,
      decide_true, ↓reduceIte] at accepted
    obtain ⟨binding, located, accepted⟩ := bind_ok accepted
    have located := mapError_ok located
    obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
    have generated := mapError_ok generated
    exact ⟨binding, lowered, (Except.ok.inj accepted).symm, located,
      GeneralizedLocalInitializerCompilation.of_accepted generated⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    {compilation : Compilation compiled.indexed named diagnostics code}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) named diagnostics code compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- Classify the real selected callback. A caller does not supply an initializer
selection or a law about any other expression invocation. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) source scope id reasonAt lowered) :
    (∃ initial binding,
      compiled.indexed.base.locals.bindings.find? (fun candidate =>
        decide (candidate.caller = named.signature.key ∧ candidate.initializer = id)) = some initial ∧
      compiled.indexed.base.locals.binding named.signature.key initial.binder.id = .ok binding ∧
      head.special = some lowered ∧
      Nonempty (Receipt (namedInputs compilation rootFuel (fuel + 1)
        (context compiled.indexed named) scope id reasonAt) binding [] lowered)) ∨
    compiled.indexed.base.locals.bindings.find? (fun candidate =>
      decide (candidate.caller = named.signature.key ∧ candidate.initializer = id)) = none := by
  cases selected : compiled.indexed.base.locals.bindings.find? (fun candidate =>
      decide (candidate.caller = named.signature.key ∧ candidate.initializer = id)) with
  | none => exact .inr rfl
  | some initial =>
    have accepted := head.selected
    rw [AcceptedNamedExpressionFlow.specialAction, root.compilerPolicy.lowerSpecial] at accepted
    obtain ⟨binding, actual, same, located, receipt⟩ :=
      of_special_output compilation selected accepted
    have output := head.result actual same
    subst actual
    exact .inl ⟨initial, binding, rfl, located, same, receipt⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualGeneralizedInitializerReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaBody
/-! A reached ordinary lambda retains its complete accepted body. Its source
position, enclosing body shape and the number of other lambdas are unrestricted.
The root budget and captured scope come from the same original compiler action. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaBody
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open AcceptedNamedExpressionFlow (Head)
open AcceptedContextualLambdaReceipt (bodyPolicy)
open AcceptedNamedBodyFlow (Body)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word}
    {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- This is the actual match context, with the final compiled data table. -/
def ambientMatch : SourceCoreCompatibleDataMatches.Context :=
  CompatibleMatchAmbientLowering.withDefinitions
    ⟨.initial compiled.compatible.checked, named.specialized.function.solvedRequirements,
      some (allocator compiled.indexed named), none⟩ compiled.indexed.layouts.definitions

private theorem assignments :
    CompatibleAssignmentStatements.AssignmentPolicy (bodyPolicy root fuel)
      (.initial compiled.compatible.checked)
      (fun site binderId => diagnostics.placeReason named.signature.key site binderId none)
      (fun site binderId operator => if operator = .equal then Word.zero
        else compilation.own.assignments.reasonAt site binderId (.value operator))
      (fun site binderId type => diagnostics.placeReason named.signature.key site binderId (some type)) := by
  refine ⟨rfl, rfl, ?_⟩
  change some _ = some _
  apply congrArg some
  funext expression fuel source scope site assignment operator rhs output next reasonAt
  cases operator <;> rfl

private theorem unary :
    CompatibleBitNotStatements.Policy (bodyPolicy root fuel)
      (.initial compiled.compatible.checked)
      (fun site binderId => diagnostics.placeReason named.signature.key site binderId none)
      (fun site binderId => compilation.own.assignments.reasonAt site binderId .bitNot)
      (fun site binderId type => diagnostics.placeReason named.signature.key site binderId (some type)) := rfl

private theorem matched :
    CompatibleMatchAmbientLowering.PolicySuccess (bodyPolicy root fuel)
      (ambientMatch (compiled := compiled) (named := named)) := by
  apply CompatibleMatchAmbientLowering.PolicySuccess.extend (by rfl)
  exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩

/-- The compiler certificate and its refined body have the identical capture
scope, parameter allocation, fuel, result type and emitted code. -/
structure Receipt
    (head : Head root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) source scope id reasonAt lowered)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId) where
  form : head.node.form = .lambda parameters result statements
  reported : Core.Ty
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id =
    .ok (head.node, reported)
  requirements : head.node.requirements = []
  coercions : head.node.coercions = []
  notInitializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  compiler : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody
    fuel (context compiled.indexed named) source scope id head.node parameters result statements
    reported reasonAt lowered
  body : Body (bodyPolicy root fuel) fuel source compiler.bodyScope statements compiler.resultCore
    reasonAt (context compiled.indexed named).internalReason
    (context compiled.indexed named).internalReason compiler.body
  ready : body.tree.Ready

/-- Every ordinary lambda action supplies the complete body receipt directly
from its accepted compiler call, including nested lambdas and nonterminal bodies. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) source scope id reasonAt lowered)
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (plain : head.special = none) (form : head.node.form = .lambda parameters result statements) :
    Nonempty (Receipt root head parameters result statements) := by
  obtain ⟨reported, read, requirements, coercions, ordinary, ⟨compiler⟩⟩ :=
    AcceptedContextualLambdaReceipt.of_head root head plain form
  have accepted := compiler.bodyCompiled
  rw [AcceptedContextualLambdaReceipt.body_callback root fuel] at accepted
  obtain ⟨body⟩ := AcceptedNamedBodyFlow.body_of_accepted accepted
  obtain ⟨tree, ready⟩ := body.tree.refine (assignments root) (unary root) (matched root)
  exact ⟨⟨form, reported, read, requirements, coercions, ordinary, compiler,
    ⟨body.flow, tree, body.emitted⟩, ready⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaInitializerReceipt
/-! A contextual lambda callback retains the actual nested initializer bundle.
Its first initializer lookup and exact catalog lookup identify the same full
binding, including the initializer used by every candidate compilation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaInitializerReceipt
open Core Frontend SourceInference SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalInitializerCompilation (Receipt)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ} {result : α}
    (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem selected_binding {catalog : Catalog} {caller : Key} {id : ExpressionId}
    {initial binding : Binding}
    (selected : catalog.bindings.find? (fun candidate =>
      decide (candidate.caller = caller ∧ candidate.initializer = id)) = some initial)
    (located : catalog.binding caller initial.binder.id = .ok binding) :
    binding = initial ∧ binding.initializer = id := by
  have member := List.mem_of_find?_eq_some selected
  have matchedKeys : initial.caller = caller ∧ initial.initializer = id := by
    simpa only [decide_eq_true_eq] using List.find?_some selected
  have present : initial ∈ catalog.bindings.filter (fun entry =>
      decide (entry.caller = caller ∧ entry.binder.id = initial.binder.id)) :=
    List.mem_filter.mpr ⟨member, by simp [matchedKeys.1]⟩
  unfold Catalog.binding at located
  generalize filtered : catalog.bindings.filter (fun entry =>
    decide (entry.caller = caller ∧ entry.binder.id = initial.binder.id)) = entries at located
  rw [filtered] at present
  cases entries with
  | nil => cases located
  | cons entry rest =>
    cases rest with
    | cons next tail => cases located
    | nil =>
      cases located
      have same : initial = binding := List.mem_singleton.mp present
      exact ⟨same.symm, same ▸ matchedKeys.2⟩

/-- These are exactly the fields updated by the accepted contextual special
branch, including its current child budget and enclosing prepared context. -/
def contextualInputs (inputs : Inputs) (prepared : SourceCoreLocalEvidence.Prepared)
    (fuel budget : Nat) (current : SourceCoreFunctions.Context)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) : Inputs :=
  { inputs with representation := GeneralizedLocalLambdaCompilation.representation inputs prepared
                current := current
                parent := some prepared
                budget := budget
                fuel := fuel
                initializer := id
                scope := scope
                reasonAt := reasonAt }

/-- The real two lookups select the same binding. No initializer-selection
law or source node shape is assumed beyond the accepted callback branch. -/
theorem of_special_output {inputs : Inputs} {prepared : SourceCoreLocalEvidence.Prepared}
    {fuel budget : Nat} {current : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {initial : Binding} {output : Option SourceCoreBasic.LoweredExpr}
    (selected : inputs.locals.bindings.find? (fun binding =>
      decide (binding.caller = current.owner ∧ binding.initializer = id)) = some initial)
    (notSelf : id ≠ inputs.initializer)
    (accepted : GeneralizedLocalLambdaCompilation.special inputs prepared fuel current child
      budget source scope id reasonAt = .ok output) :
    ∃ binding lowered, output = some lowered ∧
      inputs.locals.binding current.owner initial.binder.id = .ok binding ∧
      binding = initial ∧ binding.initializer = id ∧
      Nonempty (Receipt (contextualInputs inputs prepared fuel budget current scope id reasonAt)
        binding prepared.substitution lowered) := by
  unfold GeneralizedLocalLambdaCompilation.special at accepted
  obtain ⟨viewed, _, accepted⟩ := bind_ok accepted
  cases found : viewed.lookupExpression? id with
  | none => simp [found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  | some node =>
    simp only [found, bind, Except.bind, pure, Except.pure] at accepted
    have different : inputs.initializer ≠ id := Ne.symm notSelf
    simp only [selected, Option.filter_some, ne_eq, Option.some.injEq, different,
      not_false_eq_true, decide_true, ↓reduceIte] at accepted
    obtain ⟨binding, located, accepted⟩ := bind_ok accepted
    have located := mapError_ok located
    obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
    have generated := mapError_ok generated
    obtain ⟨same, initializer⟩ := selected_binding selected located
    exact ⟨binding, lowered, (Except.ok.inj accepted).symm, located, same, initializer,
      GeneralizedLocalInitializerCompilation.of_accepted generated⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualLambdaInitializerReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedContextualSpecialActions
/-! The original special callback selects one of four actual actions. In
particular, generalized reads retain their contextual source and native view
without assuming an empty metadata list or equality with an unnormalized node. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualSpecialActions
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes (special)
open GeneralizedLocalInitializerCompilation (namedInputs)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compilation : Compilation prepared named diagnostics code)

abbrev initializer (current : SourceCoreFunctions.Context) (id : ExpressionId) :=
  prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = current.owner ∧ binding.initializer = id))

abbrev evidence (current : SourceCoreFunctions.Context) (child : SourceCoreFunctions.ExpressionLowerer)
    (budget : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) :=
  SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
    ((representation prepared).atContext named.signature.key []).expressions.projectType
    named.specialized current child budget source scope id reasonAt
    (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])

def LocalAbsent (current : SourceCoreFunctions.Context) (node : ExpressionNode) : Prop :=
  match node.form with
  | .reference _ (.local binder) =>
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = current.owner ∧ binding.binder.id = binder)) = false
  | _ => True

/-- Every alternative retains the exact action and its output. Initializer rows
are ordered; local reads retain the complete selected substitution and slot. -/
inductive Receipt (compilation : Compilation prepared named diagnostics code)
    (rootFuel : Nat) (current : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) : Option SourceCoreBasic.LoweredExpr → Prop where
  | initialized {initial binding lowered}
      (selected : initializer (prepared := prepared) current id = some initial)
      (located : prepared.base.locals.binding current.owner initial.binder.id = .ok binding)
      (bundle : Nonempty (GeneralizedLocalInitializerCompilation.Receipt
        (namedInputs compilation rootFuel budget current scope id reasonAt) binding [] lowered)) :
      Receipt compilation rootFuel current child budget source scope id reasonAt (some lowered)
  | evidenced {viewed node lowered}
      (contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        current.plan prepared.base.locals current.owner none source id = .ok viewed)
      (found : viewed.lookupExpression? id = some node)
      (notInitializer : initializer (prepared := prepared) current id = none)
      (generated : evidence (prepared := prepared) (named := named) current child budget
        viewed scope id reasonAt = .ok (some lowered)) :
      Receipt compilation rootFuel current child budget source scope id reasonAt (some lowered)
  | generalizedRead {viewed node name binder raw lowered}
      (contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        current.plan prepared.base.locals current.owner none source id = .ok viewed)
      (found : viewed.lookupExpression? id = some node)
      (form : node.form = .reference name (.local binder))
      (notInitializer : initializer (prepared := prepared) current id = none)
      (noEvidence : evidence (prepared := prepared) (named := named) current child budget
        viewed scope id reasonAt = .ok none)
      (registered : prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = current.owner ∧ binding.binder.id = binder)) = true)
      (readAccepted : SourceCoreLocalPolymorphism.lowerRead prepared.base.locals
        current.owner [] viewed scope id (reasonAt id) = .ok raw)
      (read : Nonempty (GeneralizedLocalReadReceipts.Certificate prepared.base.locals
        current.owner [] viewed scope id (reasonAt id) raw))
      (viewAccepted : ((representation prepared).atContext named.signature.key []).localReadView
        current.owner [] viewed scope id raw = .ok lowered)
      (type : raw.type = lowered.type) :
      Receipt compilation rootFuel current child budget source scope id reasonAt (some lowered)
  | plain {viewed node}
      (contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        current.plan prepared.base.locals current.owner none source id = .ok viewed)
      (found : viewed.lookupExpression? id = some node)
      (notInitializer : initializer (prepared := prepared) current id = none)
      (noEvidence : evidence (prepared := prepared) (named := named) current child budget
        viewed scope id reasonAt = .ok none)
      (noLocal : LocalAbsent (prepared := prepared) current node) :
      Receipt compilation rootFuel current child budget source scope id reasonAt none

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {change : ε → δ}
    {result : α} (accepted : action.mapError change = .ok result) : action = .ok result := by
  cases action with
  | error error => cases accepted
  | ok value => cases accepted; rfl

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

/-- Invert the real callback, including normalized source selection, evidence,
generalized bundle selection and the final indexed view. No syntax scan is used. -/
theorem of_special {rootFuel budget : Nat} {current : SourceCoreFunctions.Context}
    {child : SourceCoreFunctions.ExpressionLowerer} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reasonAt : ExpressionId → Word}
    {output : Option SourceCoreBasic.LoweredExpr}
    (accepted : special compilation rootFuel current child budget source scope id reasonAt = .ok output) :
    Receipt compilation rootFuel current child budget source scope id reasonAt output := by
  cases selected : initializer (prepared := prepared) current id with
  | some initial =>
    obtain ⟨binding, lowered, same, located, bundle⟩ :=
      AcceptedContextualGeneralizedInitializerReceipt.of_special_output compilation selected accepted
    subst output
    exact .initialized selected located bundle
  | none =>
    unfold special at accepted
    obtain ⟨viewed, contextual, accepted⟩ := bind_ok accepted
    cases found : viewed.lookupExpression? id with
    | none => simp [found, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
    | some node =>
      simp only [found, bind, Except.bind, pure, Except.pure, selected, Option.filter_none] at accepted
      obtain ⟨optional, generated, accepted⟩ := bind_ok accepted
      cases optional with
      | some lowered =>
        cases accepted
        exact .evidenced contextual found selected generated
      | none =>
        simp only at accepted
        cases form : node.form <;> simp only [form] at accepted
        all_goals
          first
          | (cases accepted; exact .plain contextual found selected generated (by simp [LocalAbsent, form]))
          | skip
        next name resolution =>
          cases resolution <;> simp only at accepted
          all_goals
            first
            | (cases accepted; exact .plain contextual found selected generated (by simp [LocalAbsent, form]))
            | skip
          next binder =>
            cases registered : prepared.base.locals.bindings.any (fun binding =>
                decide (binding.caller = current.owner ∧ binding.binder.id = binder)) with
            | false =>
              simp only [registered, Bool.false_eq_true, ↓reduceIte] at accepted
              cases accepted
              exact .plain contextual found selected generated (by simpa [LocalAbsent, form] using registered)
            | true =>
              simp only [registered, ↓reduceIte] at accepted
              obtain ⟨raw, readAccepted, accepted⟩ := bind_ok accepted
              have readAccepted := mapError_ok readAccepted
              obtain ⟨lowered, viewAccepted, accepted⟩ := bind_ok accepted
              obtain ⟨checkedType, type, accepted⟩ := bind_ok accepted
              cases checkedType
              cases accepted
              exact .generalizedRead contextual found form selected generated registered readAccepted
                (GeneralizedLocalReadReceipts.of_accepted readAccepted) viewAccepted (ensure_type type)

/-- Every reached head observes the same root callback at its actual child
budget; this classifier introduces no separate initializer or local-read law. -/
theorem of_head {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    {compilation : Compilation compiled.indexed named diagnostics code}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word}
    {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) named diagnostics code compilation rootFuel rootSource rootScope
      rootId rootReasonAt rootLowered)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (head : AcceptedNamedExpressionFlow.Head root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) source scope id reasonAt lowered) :
    Receipt compilation rootFuel (context compiled.indexed named)
      (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child root.selected.policy
        root.selected.lowerBody fuel (context compiled.indexed named))
      (fuel + 1) source scope id reasonAt head.special := by
  have accepted := head.selected
  rw [AcceptedNamedExpressionFlow.specialAction, root.compilerPolicy.lowerSpecial] at accepted
  exact of_special compilation accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualSpecialActions
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedActionTrace
/-! Every successful contextual action of a real cached row supplies the same
root policy, selected special action and any reached ordinary lambda body.
There is no independent metadata scan, initializer selection or body profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedActionTrace
open Core Frontend SourceInference
open CallableIndexedNamedGeneration

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

structure Receipt (compilation : Compilation compiled.indexed named diagnostics code)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  predecessor : Nat
  budget : fuel = predecessor + 1
  root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
    (compiled := compiled) named diagnostics code compilation predecessor source scope id reasonAt lowered
  head : AcceptedNamedExpressionFlow.Head root.selected.policy root.selected.lowerBody predecessor
    (context compiled.indexed named) source scope id reasonAt lowered
  action : AcceptedContextualSpecialActions.Receipt compilation predecessor
    (context compiled.indexed named)
    (CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child root.selected.policy
      root.selected.lowerBody predecessor (context compiled.indexed named))
    (predecessor + 1) source scope id reasonAt head.special
  lambdaBody : ∀ parameters result statements,
    head.special = none → head.node.form = .lambda parameters result statements →
    Nonempty (AcceptedContextualLambdaBody.Receipt root head parameters result statements)

/-- The literal accepted call, with its actual specialization record, constructs
the complete action receipt. All branch selection facts are derived inside. -/
theorem of_contextual (compilation : Compilation compiled.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key [])
      compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals compilation.parents
      compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none fuel source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt compilation fuel source scope id reasonAt lowered) := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ predecessor =>
    obtain ⟨root⟩ := CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      compilation record accepted
    obtain ⟨head⟩ := AcceptedNamedExpressionFlow.Head.of_accepted root.selected.accepted
    exact ⟨⟨predecessor, rfl, root, head, AcceptedContextualSpecialActions.of_head root head,
      fun _ _ _ plain form => AcceptedContextualLambdaBody.of_head root head plain form⟩⟩

/-- All final cache rows, including methods and rows added by preparation, retain
their real named compilation and the action receipts for every accepted call. -/
theorem at_cache {index : Nat}
    (position : compiled.indexed.base.functions[index]? = some named) :
    ∃ diagnostics code, compiled.indexed.secondPass.closures[index]? = some code ∧
      ∃ compilation : Compilation compiled.indexed named diagnostics code,
        ∀ (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
          (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr),
          SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
            ((representation compiled.indexed).atContext named.signature.key [])
            compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals compilation.parents
            compilation.own.assignments diagnostics (context compiled.indexed named)
            compiled.indexed.base.callableContext none none fuel source scope id reasonAt = .ok lowered →
          Nonempty (Receipt compilation fuel source scope id reasonAt lowered) := by
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ := compiled_at compiled.indexed position
  refine ⟨diagnostics, code, cached, compilation, ?_⟩
  intro fuel source scope id reasonAt lowered accepted
  exact of_contextual compilation
    (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled position) accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedActionTrace
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedNamedGeneralizedInitializer
/-! Every actual cache position supplies its own accepted named compiler.
Each reached contextual expression then either retains the original generalized
initializer bundle or proves that the initializer override was absent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedGeneralizedInitializer
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open GeneralizedLocalInitializerCompilation (Receipt namedInputs)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}

/-- Exact receipts of the original candidate list and root/child fuel values. -/
def Outcome (compilation : Compilation compiled.indexed named diagnostics code)
    (fuel : Nat) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  (∃ predecessor, fuel = predecessor + 1 ∧ ∃ initial binding,
    compiled.indexed.base.locals.bindings.find? (fun candidate =>
      decide (candidate.caller = named.signature.key ∧ candidate.initializer = id)) = some initial ∧
    compiled.indexed.base.locals.binding named.signature.key initial.binder.id = .ok binding ∧
    Nonempty (Receipt (namedInputs compilation predecessor fuel
      (context compiled.indexed named) scope id reasonAt) binding [] lowered)) ∨
  compiled.indexed.base.locals.bindings.find? (fun candidate =>
    decide (candidate.caller = named.signature.key ∧ candidate.initializer = id)) = none

/-- The successful original contextual call constructs the selected root policy.
Its initializer selection is a result of the proof, not an input law. -/
theorem of_contextual (compilation : Compilation compiled.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      named.signature.key = .ok named.specialized)
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key [])
      compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals compilation.parents
      compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none fuel source scope id reasonAt = .ok lowered) :
    Outcome compilation fuel scope id reasonAt lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  | succ predecessor =>
    obtain ⟨root⟩ := CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt.of_accepted
      compilation record accepted
    obtain ⟨head⟩ := AcceptedNamedExpressionFlow.Head.of_accepted root.selected.accepted
    rcases AcceptedContextualGeneralizedInitializerReceipt.of_head root head with present | absent
    · obtain ⟨initial, binding, selected, located, _, receipt⟩ := present
      exact .inl ⟨predecessor, rfl, initial, binding, selected, located, receipt⟩
    · exact .inr absent

/-- Real final cache membership supplies the complete compilation witness and
exact specialization internally, including ordinary and method rows added later. -/
theorem at_cache {index : Nat}
    (position : compiled.indexed.base.functions[index]? = some named) :
    ∃ diagnostics code, compiled.indexed.secondPass.closures[index]? = some code ∧
      ∃ compilation : Compilation compiled.indexed named diagnostics code,
        ∀ (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
          (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr),
          SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
            ((representation compiled.indexed).atContext named.signature.key [])
            compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals compilation.parents
            compilation.own.assignments diagnostics (context compiled.indexed named)
            compiled.indexed.base.callableContext none none fuel source scope id reasonAt = .ok lowered →
          Outcome compilation fuel scope id reasonAt lowered := by
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ := compiled_at compiled.indexed position
  refine ⟨diagnostics, code, cached, compilation, ?_⟩
  intro fuel source scope id reasonAt lowered accepted
  exact of_contextual compilation
    (CallableIndexedOwnedPreparedOrdinaryCachedInputs.cached_record compiled position) accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedGeneralizedInitializer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedProgramBodyCompletion
/-! Static program certification can leave one actual cached root to the
compiler receipt producer. Every closure, method and other root is still checked.
Completing the exact root yields the existing full program certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProgramBodyCompletion
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedProgramAdmission

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← allProof? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

inductive Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) where
  | checked (root : RootCertificate compiled named directRows)
  | chosen (same : position = chosen)

structure Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) where
  root : Root compiled chosen position named directRows
  closures : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
    compiled named directRows allowCoerced

/-- The pending row is a member of the actual complete cache. Its exact root
is the only missing field; its closures receive the same checks as every row. -/
structure Pending (compiled : SourceCoreUnifiedCompilation.Compiled)
    (position : Nat) where
  chosen : SourceCoreGeneralFunctions.Function
  selected : compiled.indexed.base.functions[position]? = some chosen
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ pair ∈ compiled.indexed.base.functions.zipIdx,
    Nonempty (Row compiled position pair.2 pair.1 table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) :
    Option (Row compiled chosen position named directRows allowCoerced) := do
  let root ← if same : position = chosen then pure (.chosen same) else do
    let checked ← CallableIndexedOwnedPreparedProgramAdmission.certifyRoot compiled named directRows fuel
    pure (.checked checked)
  let ⟨closures⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource
    compiled named directRows allowCoerced fuel
  pure ⟨root, closures⟩

/-- This checker never invokes the root scanner for the exact chosen row.
The completed certificate still requires its authentic root proof. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (position : Nat) (fuel : Nat) :
    Option (Pending compiled position) := do
  match selected : compiled.indexed.base.functions[position]? with
  | none => none
  | some chosen =>
    if profile : compiled.compatible.checked.catalog.callableContracts = true then
      match present : compiled.indexed.base.diagnostics with
      | none => none
      | some diagnostics =>
        let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
        let selection ← certifySelection compiled table.rows fuel
        let ⟨rows⟩ ← allProof?
          (fun pair : SourceCoreGeneralFunctions.Function × Nat =>
            Nonempty (Row compiled position pair.2 pair.1 table.rows selection.allowCoerced))
          (fun pair => do
            let row ← certifyRow compiled position pair.2 pair.1 table.rows selection.allowCoerced fuel
            pure ⟨⟨row⟩⟩) compiled.indexed.base.functions.zipIdx
        pure ⟨chosen, selected, table, selection, rows, profile, diagnostics, present⟩
    else none

/-- Every completed root is either checked at its own cached source or supplied
by the exact chosen-row proof. No cached entry is omitted from coverage. -/
def Pending.complete {compiled : SourceCoreUnifiedCompilation.Compiled}
    {position : Nat} (pending : Pending compiled position)
    (root : RootCertificate compiled pending.chosen pending.table.rows) : Certificate compiled := {
  table := pending.table
  selection := pending.selection
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    cases row.root with
    | checked checked => exact ⟨⟨checked, row.closures⟩⟩
    | chosen same =>
      change index = position at same
      rw [same] at found
      have exactRow : named = pending.chosen :=
        Option.some.inj (found.symm.trans pending.selected)
      cases exactRow
      exact ⟨⟨root, row.closures⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {position : Nat} (pending : Pending compiled position)
    (root : RootCertificate compiled pending.chosen pending.table.rows) :
    (pending.complete root).table = pending.table := rfl

theorem Pending.complete_selection {compiled : SourceCoreUnifiedCompilation.Compiled}
    {position : Nat} (pending : Pending compiled position)
    (root : RootCertificate compiled pending.chosen pending.table.rows) :
    (pending.complete root).selection = pending.selection := rfl

end Solcore.SourceSemantics.CoreLowering.AcceptedProgramBodyCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedProgramRootCompletion
/-! Static program certification can leave selected actual cached roots to
compiler receipt producers. Every closure, method and other root is checked.
Completing every selected position yields the existing full program certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProgramRootCompletion
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedProgramAdmission

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← allProof? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

inductive Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) where
  | checked (root : RootCertificate compiled named directRows)
  | chosen (member : position ∈ chosen)

structure Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) where
  root : Root compiled chosen position named directRows
  closures : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
    compiled named directRows allowCoerced

/-- Each requested position exists in the actual complete cache. Only its root
is pending; its closures receive the same checks as every other row. -/
structure Pending (compiled : SourceCoreUnifiedCompilation.Compiled)
    (positions : List Nat) where
  selected : ∀ position ∈ positions, ∃ named, compiled.indexed.base.functions[position]? = some named
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ pair ∈ compiled.indexed.base.functions.zipIdx,
    Nonempty (Row compiled positions pair.2 pair.1 table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) :
    Option (Row compiled chosen position named directRows allowCoerced) := do
  let root ← if member : position ∈ chosen then pure (.chosen member) else do
    let checked ← CallableIndexedOwnedPreparedProgramAdmission.certifyRoot compiled named directRows fuel
    pure (.checked checked)
  let ⟨closures⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource
    compiled named directRows allowCoerced fuel
  pure ⟨root, closures⟩

/-- All requested indices are validated before root scanning. Every selected
root is deferred while its actual closures and the rest of the cache are checked. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (positions : List Nat) (fuel : Nat) :
    Option (Pending compiled positions) := do
  let ⟨selected⟩ ← allProof?
    (fun position => ∃ named, compiled.indexed.base.functions[position]? = some named)
    (fun position => match compiled.indexed.base.functions[position]? with
      | none => none
      | some named => some ⟨⟨named, rfl⟩⟩) positions
  if profile : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
      let selection ← certifySelection compiled table.rows fuel
      let ⟨rows⟩ ← allProof?
        (fun pair : SourceCoreGeneralFunctions.Function × Nat =>
          Nonempty (Row compiled positions pair.2 pair.1 table.rows selection.allowCoerced))
        (fun pair => do
          let row ← certifyRow compiled positions pair.2 pair.1 table.rows selection.allowCoerced fuel
          pure ⟨⟨row⟩⟩) compiled.indexed.base.functions.zipIdx
      pure ⟨selected, table, selection, rows, profile, diagnostics, present⟩
  else none

/-- Completion is indexed by actual cache lookup. Every selected row receives
its own root certificate, even when rows have the same name or result type. -/
def Pending.complete {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        RootCertificate compiled named pending.table.rows) : Certificate compiled := {
  table := pending.table
  selection := pending.selection
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    cases row.root with
    | checked checked => exact ⟨⟨checked, row.closures⟩⟩
    | chosen selected => exact ⟨⟨roots index selected named found, row.closures⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        RootCertificate compiled named pending.table.rows) :
    (pending.complete roots).table = pending.table := rfl

theorem Pending.complete_selection {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        RootCertificate compiled named pending.table.rows) :
    (pending.complete roots).selection = pending.selection := rfl


/-- Compiler producers may retain data certificates in a proposition. Each
receipt is opened only inside the existing cached-row proof. -/
def Pending.complete_receipts {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows)) : Certificate compiled := {
  table := pending.table
  selection := pending.selection
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    cases row.root with
    | checked checked => exact ⟨⟨checked, row.closures⟩⟩
    | chosen selected =>
        obtain ⟨root⟩ := roots index selected named found
        exact ⟨⟨root, row.closures⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_receipts_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows)) :
    (pending.complete_receipts roots).table = pending.table := rfl

theorem Pending.complete_receipts_selection {compiled : SourceCoreUnifiedCompilation.Compiled}
    {positions : List Nat} (pending : Pending compiled positions)
    (roots : ∀ position ∈ positions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows)) :
    (pending.complete_receipts roots).selection = pending.selection := rfl

end Solcore.SourceSemantics.CoreLowering.AcceptedProgramRootCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedProgramClosureCompletion
/-! Selected actual cached roots and closure sources can be completed by
compiler receipt producers. Other rows and every method keep their finite checks.
The completed value is the existing full program certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProgramClosureCompletion
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedProgramAdmission
open AcceptedProgramRootCompletion (Root)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← allProof? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

inductive Closures (compiled : SourceCoreUnifiedCompilation.Compiled)
    (chosen : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) where
  | checked (certificate : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
      compiled named directRows allowCoerced)
  | chosen (member : position ∈ chosen)

structure Row (compiled : SourceCoreUnifiedCompilation.Compiled)
    (roots closures : List Nat) (position : Nat) (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction) (allowCoerced : Bool) where
  root : Root compiled roots position named directRows
  closures : Closures compiled closures position named directRows allowCoerced

/-- Both sets of positions refer to the complete actual cache. A deferred
closure source must later account for every original node in that same row. -/
structure Pending (compiled : SourceCoreUnifiedCompilation.Compiled)
    (rootPositions closurePositions : List Nat) where
  rootsSelected : ∀ position ∈ rootPositions,
    ∃ named, compiled.indexed.base.functions[position]? = some named
  closuresSelected : ∀ position ∈ closurePositions,
    ∃ named, compiled.indexed.base.functions[position]? = some named
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ pair ∈ compiled.indexed.base.functions.zipIdx,
    Nonempty (Row compiled rootPositions closurePositions pair.2 pair.1 table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (rootPositions closurePositions : List Nat) (position : Nat)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) :
    Option (Row compiled rootPositions closurePositions position named directRows allowCoerced) := do
  let root ← if member : position ∈ rootPositions then pure (.chosen member) else do
    let checked ← CallableIndexedOwnedPreparedProgramAdmission.certifyRoot compiled named directRows fuel
    pure (.checked checked)
  let closures ← if member : position ∈ closurePositions then pure (.chosen member) else do
    let ⟨checked⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource
      compiled named directRows allowCoerced fuel
    pure (.checked checked)
  pure ⟨root, closures⟩

/-- Deferral is authenticated by actual cache index before row checks. Direct
inventory, methods, profile and diagnostics retain their original checks. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (rootPositions closurePositions : List Nat) (fuel : Nat) :
    Option (Pending compiled rootPositions closurePositions) := do
  let ⟨rootsSelected⟩ ← allProof?
    (fun position => ∃ named, compiled.indexed.base.functions[position]? = some named)
    (fun position => match compiled.indexed.base.functions[position]? with
      | none => none
      | some named => some ⟨⟨named, rfl⟩⟩) rootPositions
  let ⟨closuresSelected⟩ ← allProof?
    (fun position => ∃ named, compiled.indexed.base.functions[position]? = some named)
    (fun position => match compiled.indexed.base.functions[position]? with
      | none => none
      | some named => some ⟨⟨named, rfl⟩⟩) closurePositions
  if profile : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
      let selection ← certifySelection compiled table.rows fuel
      let ⟨rows⟩ ← allProof?
        (fun pair : SourceCoreGeneralFunctions.Function × Nat =>
          Nonempty (Row compiled rootPositions closurePositions pair.2 pair.1 table.rows selection.allowCoerced))
        (fun pair => do
          let row ← certifyRow compiled rootPositions closurePositions pair.2 pair.1 table.rows selection.allowCoerced fuel
          pure ⟨⟨row⟩⟩) compiled.indexed.base.functions.zipIdx
      pure ⟨rootsSelected, closuresSelected, table, selection, rows, profile, diagnostics, present⟩
  else none

/-- Each supplied receipt belongs to its actual indexed row. Closure receipts
cover every original node and use the same direct inventory and coercion lane. -/
def Pending.complete_receipts {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows pending.selection.allowCoerced) : Certificate compiled := {
  table := pending.table
  selection := pending.selection
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    have closed : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
        compiled named pending.table.rows pending.selection.allowCoerced := by
      cases row.closures with
      | checked certificate => exact certificate
      | chosen selected => exact closures index selected named found
    cases row.root with
    | checked checked => exact ⟨⟨checked, closed⟩⟩
    | chosen selected =>
        obtain ⟨root⟩ := roots index selected named found
        exact ⟨⟨root, closed⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_receipts_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows pending.selection.allowCoerced) :
    (pending.complete_receipts roots closures).table = pending.table := rfl

theorem Pending.complete_receipts_selection {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows pending.selection.allowCoerced) :
    (pending.complete_receipts roots closures).selection = pending.selection := rfl

end Solcore.SourceSemantics.CoreLowering.AcceptedProgramClosureCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedProgramMethodCompletion
/-! Original method-owned rows are completed from actual compiler receipts.
The ordinary roots and closure sources retain their indexed checks, and the
method catalog keeps its independent formation and evidence-origin checks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProgramMethodCompletion
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedProgramAdmission
open AcceptedProgramRootCompletion (Root)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← allProof? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

open AcceptedProgramClosureCompletion (Row)

/-- Both sets of positions refer to the complete actual cache. A deferred
closure source must later account for every original node in that same row. -/
structure Pending (compiled : SourceCoreUnifiedCompilation.Compiled)
    (rootPositions closurePositions : List Nat) where
  rootsSelected : ∀ position ∈ rootPositions,
    ∃ named, compiled.indexed.base.functions[position]? = some named
  closuresSelected : ∀ position ∈ closurePositions,
    ∃ named, compiled.indexed.base.functions[position]? = some named
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled
  rows : ∀ pair ∈ compiled.indexed.base.functions.zipIdx,
    Nonempty (Row compiled rootPositions closurePositions pair.2 pair.1 table.rows false)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (rootPositions closurePositions : List Nat) (position : Nat)
    (named : SourceCoreGeneralFunctions.Function)
    (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) :
    Option (Row compiled rootPositions closurePositions position named directRows allowCoerced) := do
  let root ← if member : position ∈ rootPositions then pure (.chosen member) else do
    if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
        decide (named.specialized.declaration ≠ signature.id)) = true then
      pure (.checked (.excluded (fun signature member =>
        of_decide_eq_true (List.all_eq_true.mp absent signature member))))
    else do
      let checked ← CallableIndexedOwnedPreparedProgramAdmission.certifyRoot compiled named directRows fuel
      pure (.checked checked)
  let closures ← if member : position ∈ closurePositions then pure (.chosen member) else do
    let ⟨checked⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource
      compiled named directRows allowCoerced fuel
    pure (.checked checked)
  pure ⟨root, closures⟩

/-- Deferral is authenticated by actual cache index before row checks. Direct
inventory, method catalog, profile and diagnostics retain their original checks. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (rootPositions closurePositions : List Nat) (fuel : Nat) :
    Option (Pending compiled rootPositions closurePositions) := do
  let ⟨rootsSelected⟩ ← allProof?
    (fun position => ∃ named, compiled.indexed.base.functions[position]? = some named)
    (fun position => match compiled.indexed.base.functions[position]? with
      | none => none
      | some named => some ⟨⟨named, rfl⟩⟩) rootPositions
  let ⟨closuresSelected⟩ ← allProof?
    (fun position => ∃ named, compiled.indexed.base.functions[position]? = some named)
    (fun position => match compiled.indexed.base.functions[position]? with
      | none => none
      | some named => some ⟨⟨named, rfl⟩⟩) closurePositions
  if profile : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
      let ⟨catalog⟩ ← CallableIndexedOwnedPreparedOriginsMethodAdmission.certify compiled
      let ⟨rows⟩ ← allProof?
        (fun pair : SourceCoreGeneralFunctions.Function × Nat =>
          Nonempty (Row compiled rootPositions closurePositions pair.2 pair.1 table.rows false))
        (fun pair => do
          let row ← certifyRow compiled rootPositions closurePositions pair.2 pair.1 table.rows false fuel
          pure ⟨⟨row⟩⟩) compiled.indexed.base.functions.zipIdx
      pure ⟨rootsSelected, closuresSelected, table, catalog, rows, profile, diagnostics, present⟩
  else none

/-- Each supplied receipt belongs to its actual indexed row. Closure receipts
cover every original node and use the same direct inventory and original method-origin lane. Every method receipt retains its actual cache lookup. -/
def Pending.complete_receipts {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows false)
    (methods : ∀ (position : Nat) named, compiled.indexed.base.functions[position]? = some named →
      CallableIndexedOwnedPreparedScopedMethodAdmission.RowCase compiled named pending.table.rows) :
    Certificate compiled := {
  table := pending.table
  selection := .origins ⟨by
    intro named member
    obtain ⟨position, found⟩ := List.mem_iff_getElem?.mp member
    exact methods position named found⟩ pending.catalog
  rows := by
    intro named member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨row⟩ := pending.rows (named, index) (List.mk_mem_zipIdx_iff_getElem?.mpr found)
    have closed : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
        compiled named pending.table.rows false := by
      cases row.closures with
      | checked certificate => exact certificate
      | chosen selected => exact closures index selected named found
    cases row.root with
    | checked checked => exact ⟨⟨checked, closed⟩⟩
    | chosen selected =>
        obtain ⟨root⟩ := roots index selected named found
        exact ⟨⟨root, closed⟩⟩
  profile := pending.profile
  diagnostics := pending.diagnostics }

theorem Pending.complete_receipts_table {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows false)
    (methods : ∀ (position : Nat) named, compiled.indexed.base.functions[position]? = some named →
      CallableIndexedOwnedPreparedScopedMethodAdmission.RowCase compiled named pending.table.rows) :
    (pending.complete_receipts roots closures methods).table = pending.table := rfl

theorem Pending.complete_receipts_operatorCatalog {compiled : SourceCoreUnifiedCompilation.Compiled}
    {rootPositions closurePositions : List Nat}
    (pending : Pending compiled rootPositions closurePositions)
    (roots : ∀ position ∈ rootPositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        Nonempty (RootCertificate compiled named pending.table.rows))
    (closures : ∀ position ∈ closurePositions, ∀ named,
      compiled.indexed.base.functions[position]? = some named →
        CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate
          compiled named pending.table.rows false)
    (methods : ∀ (position : Nat) named, compiled.indexed.base.functions[position]? = some named →
      CallableIndexedOwnedPreparedScopedMethodAdmission.RowCase compiled named pending.table.rows) :
    (pending.complete_receipts roots closures methods).selection.operatorCatalog = .origins pending.catalog := rfl

end Solcore.SourceSemantics.CoreLowering.AcceptedProgramMethodCompletion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedInvocationResidualEntry
/-! Named invocation roots are the exact statement roots extracted by the
real compiler. Their initial residual scope is empty. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering
open Frontend SourceInference TypeSystem SourceSpecializationWorklist

namespace CallableIndexedNamedGeneration

theorem Compilation.residual_entry
    {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (receipt : Compilation prepared named diagnostics code) :
    ResidualEntryCovered (source named) (receipt.statements.map NodeId.statement) [] := by
  have covered := ResidualEntryCovered.named (source named) []
  have roots := RecursiveNamedPreparedSourceFrames.compiled_roots_eq receipt
  change (source named).roots = receipt.statements.map NodeId.statement at roots
  rwa [roots] at covered

end CallableIndexedNamedGeneration

namespace ActualBodyInvocation

theorem Index.named_residual_entry
    {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}
    {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Core.Expr}
    (receipt : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
    (selected : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      named.signature.key = .ok named.specialized) :
    let index : Index compiled bodyRelation := .named receipt selected
    ResidualEntryCovered index.source (index.statements.map NodeId.statement) index.active.domain := by
  exact receipt.residual_entry

end ActualBodyInvocation
end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationResidualEntry
/-! The existing actual invocation carries scope evidence for its original
cached body. Named calls derive it from their root receipt; contextual calls
retain the evidence produced by the real stored read. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableLambdaBodyReachability CallableBodyMetadataViews
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : BodyRelation}

/-- The same final-plan source precedes the native flexible action. -/
def Index.originalSource : Index compiled bodyRelation → TypedSource
  | @Index.named _ _ callable _ _ _ _ => callable.specialized.function.typedBody
  | .contextual material _ => material.candidate.origin.source

/-- This proof component is produced at named entry or at the actual contextual
read. It does not alter the invocation's native or Source representation. -/
def Index.ResidualEntry : Index compiled bodyRelation → Prop
  | .named _ _ => True
  | .contextual material _ => SelectedCompilationLocalReadMaterialization.Entry material

theorem Index.original_receipt (index : Index compiled bodyRelation) :
    ∃ row, SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan index.owner = .ok row ∧
      row.function.typedBody = index.originalSource := by
  cases index with
  | named receipt selected => exact ⟨_, selected, rfl⟩
  | contextual material view =>
    obtain ⟨row, selected, source, _, _⟩ :=
      LambdaSourceAlignment.prepared_source material.packet.original.emission.authentic
    rw [material.indexed.plan] at selected
    refine ⟨row, ?_, source⟩
    simpa only [Index.owner, material.compilation, GeneralizedLocalLambdaCompilation.context,
      material.indexed.owner] using selected

theorem Index.compiler_original (index : Index compiled bodyRelation) :
    index.compilerSource = index.originalSource.applySubstitution index.active := by
  cases index with
  | named receipt selected => exact (EmptySourceSubstitution.source _).symm
  | contextual material view =>
    exact SelectedCompilationLocalSourceReceipts.compiler_source material

theorem Index.ResidualEntry.covered {index : Index compiled bodyRelation}
    (entry : index.ResidualEntry) :
    ResidualEntryCovered index.originalSource (index.statements.map NodeId.statement)
      index.active.domain := by
  cases index with
  | named receipt selected => exact receipt.residual_entry
  | contextual material view =>
    exact SelectedCompilationLocalReadMaterialization.Entry.covered entry

theorem Index.reaches_original (index : Index compiled bodyRelation) {node : NodeId}
    (path : Reaches index.compilerSource (index.statements.map NodeId.statement) node) :
    Reaches index.originalSource (index.statements.map NodeId.statement) node := by
  apply (reaches_substitution index.active).mp
  rwa [← index.compiler_original]

/-- Both the invocation and the selected candidate resolve the same real key
in the final plan. This fixes the binding source before either substitution. -/
theorem Index.binding_original (index : Index compiled bodyRelation)
    {binding : SourceCoreLocalPolymorphism.Binding}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext index.active)
    (owner : binding.caller = index.owner) :
    binding.source = index.originalSource := by
  obtain ⟨candidateOwner, candidateSource, _, _⟩ :=
    SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨target, targetFound, targetSource, _, _⟩ :=
    LambdaSourceAlignment.prepared_source packet.original.emission.authentic
  rw [indexed.plan, candidateOwner, owner] at targetFound
  obtain ⟨original, originalFound, originalSource⟩ := index.original_receipt
  have same : target = original := Except.ok.inj (targetFound.symm.trans originalFound)
  exact (targetSource.trans candidateSource).symm.trans (same ▸ originalSource)

/-- Runtime statement lookup extends the original lexical path through the
actual substitution, without comparing unrelated table entries. -/
theorem Index.statement_lexical_child (index : Index compiled bodyRelation)
    {id : StatementId} {node : StatementNode} {child : NodeId}
    (path : LocalLambdaLexicalPath index.originalSource
      (index.statements.map NodeId.statement) (.statement id))
    (found : index.compilerSource.lookupStatement? id = some node)
    (edge : child ∈ node.form.references) :
    LocalLambdaLexicalPath index.originalSource (index.statements.map NodeId.statement) child := by
  rw [index.compiler_original] at found
  exact path.statement_child_of_substitution found edge

/-- A non-lambda expression extends the same original lexical path. Lambda
bodies start with their own actual invocation-entry evidence. -/
theorem Index.expression_lexical_child (index : Index compiled bodyRelation)
    {id : ExpressionId} {node : ExpressionNode} {child : NodeId}
    (path : LocalLambdaLexicalPath index.originalSource
      (index.statements.map NodeId.statement) (.expression id))
    (found : index.compilerSource.lookupExpression? id = some node)
    (nonLambda : ∀ parameters result body, node.form ≠ .lambda parameters result body)
    (edge : child ∈ node.form.references) :
    LocalLambdaLexicalPath index.originalSource (index.statements.map NodeId.statement) child := by
  rw [index.compiler_original] at found
  exact path.expression_child_of_substitution found nonLambda edge

/-- A body site keeps the executed compiler path and the original lexical
path together. The constructors below follow the actual roots and lookups. -/
structure Index.Site (index : Index compiled bodyRelation) (node : NodeId) : Prop where
  reached : index.Reached node
  lexical : LocalLambdaLexicalPath index.originalSource
    (index.statements.map NodeId.statement) node

theorem Index.site_root (index : Index compiled bodyRelation) {id : StatementId}
    (member : id ∈ index.statements) : index.Site (.statement id) :=
  ⟨index.body_root member, .root (List.mem_map.mpr ⟨id, member, rfl⟩)⟩

theorem Index.Site.statement_child {index : Index compiled bodyRelation}
    {id : StatementId} (site : index.Site (.statement id))
    {node : StatementNode} (found : index.compilerSource.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Site child :=
  ⟨.statement site.reached found edge,
    index.statement_lexical_child site.lexical found edge⟩

theorem Index.Site.expression_child {index : Index compiled bodyRelation}
    {id : ExpressionId} (site : index.Site (.expression id))
    {node : ExpressionNode} (found : index.compilerSource.lookupExpression? id = some node)
    (nonLambda : ∀ parameters result body, node.form ≠ .lambda parameters result body)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Site child :=
  ⟨.expression site.reached found edge,
    index.expression_lexical_child site.lexical found nonLambda edge⟩

/-- Source execution and native compilation share the reached statement.
This transports the same site through a genuine Source child step. -/
theorem Index.Site.statement_source_child {index : Index compiled ReachedView}
    {id : StatementId} (site : index.Site (.statement id))
    {node : StatementNode} (found : index.source.lookupStatement? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Site child := by
  apply site.statement_child _ edge
  exact (index.reached_view.statement (.inr site.reached)).symm.trans found

theorem Index.Site.expression_source_child {index : Index compiled ReachedView}
    {id : ExpressionId} (site : index.Site (.expression id))
    {node : ExpressionNode} (found : index.source.lookupExpression? id = some node)
    (nonLambda : ∀ parameters result body, node.form ≠ .lambda parameters result body)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Site child := by
  obtain ⟨actual, selected, _, form⟩ :=
    index.reached_view.expression_back (.inr site.reached) found
  apply site.expression_child selected
  · simpa only [form] using nonLambda
  · simpa only [form] using edge

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationCapturedScope
/-! Actual initialized statements capture the scope of their own invocation.
The compiler's substitution preserves the quantified variables and occurrence
identities used by this evidence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableBodyMetadataViews

private theorem statement_node {source : TypedSource} {id : StatementId}
    {node : StatementNode} (found : source.lookupStatement? id = some node) :
    source.lookupNode? id.occurrence = some (.statement node) := by
  unfold TypedSource.lookupStatement? at found
  cases selected : source.lookupNode? id.occurrence with
  | none => simp [selected] at found
  | some actual =>
    cases actual with
    | expression => simp [selected] at found
    | statement original =>
      have same : original = node := by simpa [selected] using found
      simp only [same]

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {bodyRelation : BodyRelation} {index : Index compiled bodyRelation}

theorem Index.ResidualEntry.capture_statement
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {binder : TypedBinder} {initializer : ExpressionId}
    (form : statement.form = .letDecl binder (some initializer)) :
    CapturedResidualScope index.originalSource initializer
      binder.scheme.quantified index.active.domain := by
  rw [index.compiler_original, lookupStatement_apply] at found
  obtain ⟨original, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  rcases original with ⟨originalId, span, type, actual⟩
  cases actual <;> simp only [StatementNode.applySubstitution,
    StatementForm.applySubstitution] at form <;> try contradiction
  rename_i rawBinder rawInitializer
  obtain ⟨rfl, sameInitializer⟩ := StatementForm.letDecl.inj form
  subst rawInitializer
  exact entry.covered.capture (binder := rawBinder) site.lexical (statement_node selected) rfl

private theorem initialized_item_before {active : Substitution} {items : List ForItemForm}
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : .letDecl binder (some initializer) ∈ items.map (ForItemForm.applySubstitution active)) :
    ∃ original, .letDecl original (some initializer) ∈ items ∧
      original.scheme.quantified = binder.scheme.quantified := by
  obtain ⟨original, present, same⟩ := List.mem_map.mp member
  cases original <;> simp only [ForItemForm.applySubstitution] at same <;> try contradiction
  rename_i rawBinder rawInitializer
  obtain ⟨rfl, sameInitializer⟩ := ForItemForm.letDecl.inj same
  subst rawInitializer
  exact ⟨rawBinder, present, rfl⟩

theorem Index.ResidualEntry.capture_header
    (entry : index.ResidualEntry) {id : StatementId}
    (site : index.Site (.statement id)) {statement : StatementNode}
    (found : index.compilerSource.lookupStatement? id = some statement)
    {initializers post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (form : statement.form = .forLoop initializers condition post body)
    {binder : TypedBinder} {initializer : ExpressionId}
    (member : .letDecl binder (some initializer) ∈ initializers ++ post) :
    CapturedResidualScope index.originalSource initializer
      binder.scheme.quantified index.active.domain := by
  rw [index.compiler_original, lookupStatement_apply] at found
  obtain ⟨original, selected, rfl⟩ := Option.map_eq_some_iff.mp found
  rcases original with ⟨originalId, span, type, actual⟩
  cases actual <;> simp only [StatementNode.applySubstitution,
    StatementForm.applySubstitution] at form <;> try contradiction
  obtain ⟨rfl, rfl, rfl, rfl⟩ := StatementForm.forLoop.inj form
  rw [← List.map_append] at member
  obtain ⟨rawBinder, present, same⟩ := initialized_item_before member
  rw [← same]
  exact ResidualScopeReachability.capture_header entry.covered site.lexical selected rfl present

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReadEntry
/-! Both actual invocation forms consume the same stored Snapshot and return
scope evidence for the next body. The code and saved frame remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem SourceSpecializationWorklist
open CallableBodyMetadataViews GeneralizedLocalAcceptedMaterialization
open SelectedCompilationLocalReadMaterialization (Entry)

theorem Index.materialize_read
    {workspace : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram workspace fuel = .ok compiled.program)
    (index : Index cached ReachedView) (entry : index.ResidualEntry)
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : GeneralizedLocalReadReceipts.Certificate cached.indexed.base.locals
      index.owner index.active index.compilerSource scope id reason lowered)
    (site : index.Site (.expression id))
    {descriptor : Dynamic.GeneralizedClosure} {lexical : Substitution}
    {frameLocation : Core.Location} {native : Value} {attachment : Prop}
    (row : GeneralizedLocalAcceptedInstances.Snapshot cached.indexed mapping world descriptor
      receipt.binding lexical frameLocation attachment receipt.candidate native)
    (saved : GeneralizedLocalCapturedScopes.Attachment descriptor receipt.binding lexical)
    (extension : GeneralizedLocalBundleContexts.ContextExtension lexical index.active)
    (captures : Dynamic.GeneralizedClosureCaptures descriptor.definitionContext descriptor.source
      descriptor.captured descriptor.binder descriptor.initializer descriptor)
    (unique : NodeOccurrencesUnique descriptor.source)
    (initializer : descriptor.initializer = receipt.binding.initializer)
    {context : Solcore.SourceSemantics.Context} {callerEvidence produced : Dynamic.EvidenceEnvironment}
    {actualType : TypeSystem.Ty} {requirements : List RequirementId} {semantic : TypeSystem.Substitution}
    (instantiation : Dynamic.LocalSchemeRuntimeInstantiation context callerEvidence descriptor.binder
      actualType requirements semantic produced)
    (sameScheme : descriptor.binder.scheme = receipt.binding.binder.scheme.apply index.active)
    (sameType : actualType = receipt.node.rawType) :
    let function := descriptor.instantiate semantic (produced ++ callerEvidence.applySubstitution semantic)
    ∃ material : Materialization cached mapping world function
        (fun source view => BodyView source view (function.body.map NodeId.statement)),
      material.descriptor = descriptor ∧ material.binding = receipt.binding ∧ material.lexical = lexical ∧
      material.candidate = receipt.candidate ∧ material.actualType = actualType ∧ material.semantic = semantic ∧
      material.context = context ∧ material.callerEvidence = callerEvidence ∧ material.produced = produced ∧
      material.requirements = requirements ∧ material.frameLocation = frameLocation ∧ Entry material ∧
      native = CallableIndexedLambdaValues.value material.code material.captured.embedding
        material.origin.native material.actual := by
  cases index with
  | named receiptNamed selected =>
    exact SelectedCompilationNamedReadMaterialization.materialize_at_named_read receipt row saved
      extension captures unique initializer instantiation sameScheme sameType
  | contextual caller view =>
    exact SelectedCompilationLocalReadMaterialization.materialize_at_contextual_read artifact checked
      caller entry receipt site.reached row saved extension captures unique initializer
      instantiation sameScheme sameType

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
end
