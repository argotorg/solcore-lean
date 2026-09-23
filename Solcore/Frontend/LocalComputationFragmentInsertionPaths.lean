import Solcore.Frontend.LocalComputationFragment
import Solcore.Core.LocalFragment
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Frontend.WordLessCostStepComposition

/-! One shared cost precedes every outer continuation. Each caller retains its
own saved frames, while an actual closure's body path is reused unchanged. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalComputationFragment.insertion_paths
    {expr : Core.Expr} (fragment : LocalComputationFragment expr)
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
  | pure child => exact child.insertion_paths leading suffix inserted evaluation
  | application callee operand =>
      cases evaluation with
      | apply functionEvaluation argumentEvaluation bodyEvaluation =>
          obtain ⟨functionCost, functionPaths⟩ := callee.insertion_paths leading suffix inserted functionEvaluation
          obtain ⟨argumentCost, argumentPaths⟩ := operand.insertion_paths leading suffix inserted argumentEvaluation
          obtain ⟨bodyCost, bodyPath⟩ := bodyEvaluation.toSteps
          refine ⟨functionCost + argumentCost + bodyCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.apply (functionPaths _).1 (argumentPaths _).1 bodyPath
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.apply (functionPaths _).2 (argumentPaths _).2 bodyPath
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
