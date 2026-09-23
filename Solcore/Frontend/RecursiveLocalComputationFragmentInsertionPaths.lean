import Solcore.Frontend.RecursiveLocalComputationFragment
import Solcore.Core.LocalFragment
import Solcore.Frontend.LocalFunctionApplicationStepComposition
import Solcore.Frontend.LocalExpressionCostStepComposition
import Solcore.Frontend.WordLessCostStepComposition

/-! Each recursive caller pair shares one cost before every continuation.
An actual invoked body's closed path is chosen once and reused on both sides.
Let-body paths retain the same actual bound value before the caller prefix. -/

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
  induction fragment generalizing leading initialStore finalStore value with
  | pure child => exact child.insertion_paths leading suffix inserted evaluation
  | application _ _ calleeIH operandIH =>
      cases evaluation with
      | apply functionEvaluation argumentEvaluation bodyEvaluation =>
          obtain ⟨functionCost, functionPaths⟩ := calleeIH leading functionEvaluation
          obtain ⟨argumentCost, argumentPaths⟩ := operandIH leading argumentEvaluation
          obtain ⟨bodyCost, bodyPath⟩ := bodyEvaluation.toSteps
          refine ⟨functionCost + argumentCost + bodyCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.apply (functionPaths _).1 (argumentPaths _).1 bodyPath
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.apply (functionPaths _).2 (argumentPaths _).2 bodyPath
  | pair _ _ leftIH rightIH =>
      cases evaluation with
      | pair left right =>
          obtain ⟨leftCost, leftPaths⟩ := leftIH leading left
          obtain ⟨rightCost, rightPaths⟩ := rightIH leading right
          refine ⟨leftCost + rightCost + 3, fun continuation => ?_⟩
          constructor
          · have path := Core.Steps.cons (.enterPair (continuation := continuation))
              ((leftPaths _).1.trans (.cons .enterPairRight
                ((rightPaths _).1.trans (.cons .applyPair .refl))))
            simpa only [Nat.add_assoc] using path
          · simp only [Core.Expr.weakenAt]
            have path := Core.Steps.cons (.enterPair (continuation := continuation))
              ((leftPaths _).2.trans (.cons .enterPairRight
                ((rightPaths _).2.trans (.cons .applyPair .refl))))
            simpa only [Nat.add_assoc] using path
  | binary _ _ leftIH rightIH =>
      cases evaluation with
      | binary leftEvaluation rightEvaluation applied =>
          obtain ⟨leftCost, leftPaths⟩ := leftIH leading leftEvaluation
          obtain ⟨rightCost, rightPaths⟩ := rightIH leading rightEvaluation
          refine ⟨leftCost + rightCost + 3, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.binary (leftPaths _).1 (rightPaths _).1 applied
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.binary (leftPaths _).2 (rightPaths _).2 applied
  | ifE _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := conditionIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := thenIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.ifTrue (conditionPaths _).1 (branchPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.ifTrue (conditionPaths _).2 (branchPaths _).2
      | ifFalse condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := conditionIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := elseIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.ifFalse (conditionPaths _).1 (branchPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.ifFalse (conditionPaths _).2 (branchPaths _).2
  | unary _ childIH =>
      cases evaluation with
      | unary child applied =>
          obtain ⟨childCost, childPaths⟩ := childIH leading child
          refine ⟨childCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.unary (childPaths _).1 applied
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.unary (childPaths _).2 applied
  | letE _ _ initializerIH bodyIH =>
      cases evaluation with
      | @letE _ _ _ _ _ _ boundValue _ initializer body =>
          obtain ⟨initializerCost, initializerPaths⟩ := initializerIH leading initializer
          obtain ⟨bodyCost, bodyPaths⟩ := bodyIH (boundValue :: leading) body
          refine ⟨initializerCost + bodyCost + 2, fun continuation => ?_⟩
          constructor
          · exact CostStepComposition.letE (initializerPaths _).1 (bodyPaths _).1
          · simp only [Core.Expr.weakenAt]
            exact CostStepComposition.letE (initializerPaths _).2 (bodyPaths _).2

end Solcore.Frontend
