import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts

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
