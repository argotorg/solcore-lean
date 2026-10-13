import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
import Solcore.SourceSemantics.CoreLowering.AcceptedContextualDirectReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles

/-! The selected contextual hook retains its actual overloaded operator method
and ordered operand actions. Initializer selection remains an exact alternative. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualOperatorReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)
open AcceptedNamedExpressionFlow (Head specialAction)

def Form (form : ExpressionForm) : Prop :=
  (∃ operator operand, form = .unary operator operand) ∨
    (∃ operator left right, form = .binary left operator right)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Only the actual selected callback is inspected. The original source is not
rewritten, and the method dictionary is retained by the existing receipt. -/
theorem of_special
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode)
    {rootFuel fuel : Nat} {policy : SourceCoreFunctions.Policy}
    {body : SourceCoreFunctions.BodyLowerer} {current : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr}
    (recipe : PolicyRecipe compilation rootFuel policy)
    (found : source.lookupExpression? id = some node)
    (form : Form node.form) (coercions : node.coercions = [])
    (accepted : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower current (Child policy body fuel current)
          (fuel + 1) source scope id reasonAt) = .ok (some output)) :
    Nonempty (CallablePreparedMethodSelection.Operator prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id reasonAt (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) node output) ∨
      Nonempty (AcceptedContextualDirectReceipt.InitializerAt prepared current id) := by
  rw [recipe.lowerSpecial] at accepted
  change special compilation rootFuel current (Child policy body fuel current)
    (fuel + 1) source scope id reasonAt = .ok (some output) at accepted
  have sameSource : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      current.plan prepared.base.locals current.owner none source id = .ok source := by
    rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
    all_goals simp [SourceCoreGeneralFunctions.contextualSource, found, original]
  unfold special at accepted
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure] at accepted
  cases selected : (prepared.base.locals.bindings.find? fun candidate =>
      decide (candidate.caller = current.owner ∧ candidate.initializer = id)).filter
        (fun _ => (none : Option ExpressionId) ≠ some id) with
  | some binding => exact .inr ⟨⟨binding, selected⟩⟩
  | none =>
    rw [selected] at accepted
    cases evidence : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized current (Child policy body fuel current) (fuel + 1)
        source scope id reasonAt (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => simp [evidence] at accepted
    | ok value =>
      cases value with
      | none =>
        rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
        all_goals simp [evidence, original] at accepted
      | some result =>
        simp only [evidence] at accepted
        cases accepted
        have ordinary := CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.ordinary_requirements coercions
        have nonempty : node.requirements ≠ [] := by
          intro empty
          rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
          all_goals simp [SourceCoreEvidence.lowerWithProjector, found, original, ordinary, coercions, empty] at evidence
        exact .inl (CallablePreparedMethodSelection.of_accepted found form ordinary nonempty evidence)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- The existing method receipt records the original parent output and the
actual recursive child callback at this budget. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (selected : head.special = some lowered)
    (form : Form head.node.form) (coercions : head.node.coercions = []) :
    Nonempty (CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
      root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      (.initial compiled.compatible.checked) source scope id reasonAt lowered) ∨
      Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id) := by
  have accepted := head.selected.trans (congrArg Except.ok selected)
  cases of_special compilation root.compilerPolicy head.found form coercions accepted with
  | inr initializer => exact .inr initializer
  | inl methods =>
    obtain ⟨method⟩ := methods
    have projected := method.suffix.outputProjection
    change SourceCoreCompatibleDataExpressions.projectType compiled.compatible.checked
      (.occurrence head.node.id.occurrence) head.node.type = .ok lowered.type at projected
    have actualPolicy : CallablePreparedMethodSelection.Operator compiled.indexed.base.sourceProgram
        ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
        named.specialized (context compiled.indexed named)
        (Child root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named))
        (fuel + 1) source scope id reasonAt root.selected.policy.callables head.node lowered := by
      rw [root.selected.callables]
      exact method
    exact .inl (CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.of_evidence
      coercions (CompatibleExpressionReads.projectType_of_accepted projected) actualPolicy accepted head.accepted)

/-- Ordinary compatible acceptance forces empty original requirements. This
excludes that exact branch at the fixture's authentic method occurrences. -/
theorem plain_requirements
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none) (form : Form head.node.form) : head.node.requirements = [] := by
  have sameSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals
      (context compiled.indexed named).owner none source id = .ok source := by
    rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
    all_goals simp [SourceCoreGeneralFunctions.contextualSource, head.found, original]
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
    rcases form with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
  all_goals
    simp only [original] at accepted
    obtain ⟨pair, read, _⟩ := bind_ok accepted
    obtain ⟨node, type⟩ := pair
    have actual := CompatibleExpressionReads.metadata_of_read (readPolicy ▸ read)
    have same := Option.some.inj (actual.found.symm.trans head.found)
    subst node
    exact actual.requirements

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualOperatorReceipt
