import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow

/-! Ordinary indirect acceptance retains the actual callee and ordered argument
actions. Compatible reads and the original successful guard recover metadata;
the same contextual callback supplies genuine initializer exclusion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedIndirectExpressionReceipt
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
  {fuel : Nat} {id callee : ExpressionId} {arguments : List ExpressionId}
  {metadata : IndirectCallResolution} {lowered : SourceCoreBasic.LoweredExpr}

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem initializer_none
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .call callee arguments (.indirect metadata)) :
    compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none := by
  have accepted := head.selected
  rw [plain] at accepted
  unfold specialAction at accepted
  rw [root.compilerPolicy.lowerSpecial] at accepted
  have sameSource := CallableIndexedOwnedIndirectCompilerPolicyInputs.contextualSource_indirect
    compiled.indexed.base.sourceProgram (context compiled.indexed named).plan
    compiled.indexed.base.locals (context compiled.indexed named).owner none head.found form
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
    (form : head.node.form = .call callee arguments (.indirect metadata)) :
    ∃ type, root.selected.policy.readExpression source id = .ok (head.node, type) ∧
      CompatibleExpressionReads.Metadata compiled.compatible.checked source id head.node type ∧
      metadata.argumentCoercions = [] := by
  have sameSource := CallableIndexedOwnedIndirectCompilerPolicyInputs.contextualSource_indirect
    compiled.indexed.base.sourceProgram (context compiled.indexed named).plan
    compiled.indexed.base.locals (context compiled.indexed named).owner none head.found form
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
    simp only [form] at accepted
    by_cases empty : metadata.argumentCoercions.isEmpty = true
    · exact ⟨type, read, actual, List.isEmpty_iff.mp empty⟩
    · simp [empty] at accepted

/-- No grammar or universal hook premise is required. Both delegation fields
of the existing receipt are derived from this actual ordinary compiler action. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .call callee arguments (.indirect metadata)) :
    Nonempty (CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody
      fuel (context compiled.indexed named) source scope id callee arguments metadata reasonAt lowered) := by
  have ordinary := initializer_none root head plain form
  obtain ⟨type, read, actual, noArgumentCoercions⟩ := ordinary_metadata root head plain form
  have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root
    (scope := scope) (reasonAt := reasonAt)
    head.found form actual.requirements actual.coercions noArgumentCoercions ordinary
  exact CallableIndirectCallCertificates.of_functions head.found form profile.special read form head.accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedIndirectExpressionReceipt
