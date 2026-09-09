import Solcore.Frontend.RecursiveLocalComputationFragment
import Solcore.Core.LocalFragmentInsertionPaths
import Solcore.Frontend.LocalFunctionApplicationStepComposition

/-! Each recursive caller pair shares one cost before every continuation.
An actual invoked body's closed path is chosen once and reused on both sides. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RecursiveLocalComputationFragment.insertion_paths
    {expr : Core.Expr} (fragment : RecursiveLocalComputationFragment expr)
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
  induction fragment generalizing initialStore finalStore value with
  | pure child => exact child.insertion_paths leading suffix inserted evaluation
  | application _ _ calleeIH operandIH =>
      cases evaluation with
      | apply functionEvaluation argumentEvaluation bodyEvaluation =>
          obtain ⟨functionCost, functionPaths⟩ := calleeIH functionEvaluation
          obtain ⟨argumentCost, argumentPaths⟩ := operandIH argumentEvaluation
          obtain ⟨bodyCost, bodyPath⟩ := bodyEvaluation.toSteps
          refine ⟨functionCost + argumentCost + bodyCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.apply (functionPaths _).1 (argumentPaths _).1 bodyPath
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.apply (functionPaths _).2 (argumentPaths _).2 bodyPath

end Solcore.Frontend
