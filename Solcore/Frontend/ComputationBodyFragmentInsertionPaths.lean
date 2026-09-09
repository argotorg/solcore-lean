import Solcore.Frontend.ComputationBodyFragment
import Solcore.Frontend.WordLessCostStepComposition

/-! One literal outcome and one cost are shared before every continuation.
Only the child's paired-path law is required, not its typing or raw insertion. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationBodyFragment.insertion_paths {F : Core.Expr → Prop}
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    {expr : Core.Expr} (fragment : ComputationBodyFragment F expr)
    (leading suffix : Core.Environment) (inserted : Core.Value)
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (evaluation : Core.Evaluates (leading ++ suffix) initialStore expr value finalStore) :
    ∃ cost, ∀ continuation,
      Core.Steps cost
        ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Core.Steps cost
        ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  induction fragment generalizing leading initialStore finalStore value with
  | unit =>
      cases evaluation
      exact ⟨1, fun _ => ⟨.cons .unit .refl, by simpa only [Core.Expr.weakenAt] using (Core.Steps.cons Core.Transition.unit .refl)⟩⟩
  | leaf child => exact childPaths child leading suffix inserted evaluation
  | letE _ _ headIH tailIH =>
      cases evaluation with
      | @letE _ _ _ _ _ _ boundValue _ head tail =>
          obtain ⟨headCost, headPaths⟩ := headIH leading head
          obtain ⟨tailCost, tailPaths⟩ := tailIH (boundValue :: leading) tail
          refine ⟨headCost + tailCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.letE (headPaths _).1 (tailPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.letE (headPaths _).2 (tailPaths _).2
  | ifE _ _ _ guardIH yesIH noIH =>
      cases evaluation with
      | ifTrue condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := guardIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := yesIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.ifTrue (conditionPaths _).1 (branchPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.ifTrue (conditionPaths _).2 (branchPaths _).2
      | ifFalse condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := guardIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := noIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.ifFalse (conditionPaths _).1 (branchPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.ifFalse (conditionPaths _).2 (branchPaths _).2

end Solcore.Frontend
