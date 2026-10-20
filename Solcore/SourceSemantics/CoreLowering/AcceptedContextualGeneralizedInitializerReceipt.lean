import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalInitializerCompilation
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionTree

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
