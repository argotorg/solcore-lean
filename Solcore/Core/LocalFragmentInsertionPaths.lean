import Solcore.Core.LocalFragment
import Solcore.Core.Correspondence

/-! Paired exact-cost paths for the local Core fragment. A common cost is
chosen before the arbitrary outer continuation. Each side constructs its own
internal frames and saved environments; no equality of states is asserted. -/

set_option autoImplicit false

namespace Solcore.Core

private theorem lookup_insert (leading suffix : Environment) (inserted : Value) (index : Nat) :
    (leading ++ inserted :: suffix)[if leading.length ≤ index then index + 1 else index]? =
      (leading ++ suffix)[index]? := by
  induction leading generalizing index with
  | nil => simp
  | cons head leading ih =>
      cases index with
      | zero => simp
      | succ index =>
          by_cases shifted : leading.length ≤ index <;>
            simpa [shifted, Nat.succ_le_succ_iff] using ih index

private theorem unary_path {environment : Environment} {initialStore finalStore : Store}
    {op : UnaryOp} {operand : Expr} {operandValue result : Value}
    {continuation : List Frame} {childCost : Nat}
    (child : Steps childCost
      ⟨.eval operand environment, .unaryApply op :: continuation, initialStore⟩
      ⟨.ret operandValue, .unaryApply op :: continuation, finalStore⟩)
    (applied : op.apply operandValue = some result) :
    Steps (childCost + 2)
      ⟨.eval (.unary op operand) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterUnary (child.trans (.cons (.applyUnary applied) .refl))
  simpa only [Nat.add_assoc] using path

private theorem binary_path {environment : Environment} {initialStore middleStore finalStore : Store}
    {op : BinaryOp} {left right : Expr} {leftValue rightValue result : Value}
    {continuation : List Frame} {leftCost rightCost : Nat}
    (leftPath : Steps leftCost
      ⟨.eval left environment, .binaryRight op right environment :: continuation, initialStore⟩
      ⟨.ret leftValue, .binaryRight op right environment :: continuation, middleStore⟩)
    (rightPath : Steps rightCost
      ⟨.eval right environment, .binaryApply op leftValue :: continuation, middleStore⟩
      ⟨.ret rightValue, .binaryApply op leftValue :: continuation, finalStore⟩)
    (applied : op.apply leftValue rightValue = some result) :
    Steps (leftCost + rightCost + 3)
      ⟨.eval (.binary op left right) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterBinary
    (leftPath.trans (.cons .enterBinaryRight (rightPath.trans (.cons (.applyBinary applied) .refl))))
  simpa only [Nat.add_assoc] using path

private theorem let_path {environment : Environment} {initialStore middleStore finalStore : Store}
    {value body : Expr} {boundValue result : Value} {continuation : List Frame}
    {valueCost bodyCost : Nat}
    (valuePath : Steps valueCost
      ⟨.eval value environment, .letBody body environment :: continuation, initialStore⟩
      ⟨.ret boundValue, .letBody body environment :: continuation, middleStore⟩)
    (bodyPath : Steps bodyCost
      ⟨.eval body (boundValue :: environment), continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (valueCost + bodyCost + 2)
      ⟨.eval (.letE value body) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterLet (valuePath.trans (.cons .bindLet bodyPath))
  simpa only [Nat.add_assoc] using path

private theorem if_true_path {environment : Environment} {initialStore middleStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value}
    {continuation : List Frame} {conditionCost branchCost : Nat}
    (conditionPath : Steps conditionCost
      ⟨.eval condition environment, .ifBranches thenBranch elseBranch environment :: continuation, initialStore⟩
      ⟨.ret (.bool true), .ifBranches thenBranch elseBranch environment :: continuation, middleStore⟩)
    (branchPath : Steps branchCost
      ⟨.eval thenBranch environment, continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (conditionCost + branchCost + 2)
      ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterIf (conditionPath.trans (.cons .chooseTrue branchPath))
  simpa only [Nat.add_assoc] using path

private theorem if_false_path {environment : Environment} {initialStore middleStore finalStore : Store}
    {condition thenBranch elseBranch : Expr} {result : Value}
    {continuation : List Frame} {conditionCost branchCost : Nat}
    (conditionPath : Steps conditionCost
      ⟨.eval condition environment, .ifBranches thenBranch elseBranch environment :: continuation, initialStore⟩
      ⟨.ret (.bool false), .ifBranches thenBranch elseBranch environment :: continuation, middleStore⟩)
    (branchPath : Steps branchCost
      ⟨.eval elseBranch environment, continuation, middleStore⟩
      ⟨.ret result, continuation, finalStore⟩) :
    Steps (conditionCost + branchCost + 2)
      ⟨.eval (.ifE condition thenBranch elseBranch) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have path := Steps.cons .enterIf (conditionPath.trans (.cons .chooseFalse branchPath))
  simpa only [Nat.add_assoc] using path

/-- Successful local evaluation gives original and inserted paths with one
shared cost, independent of the untouched outer continuation. Values and both
stores are exact; typing, scope, freshness and runtime-world premises are absent. -/
theorem Expr.LocalFragment.insertion_paths
    {expr : Expr} (fragment : expr.LocalFragment)
    (leading suffix : Environment) (inserted : Value)
    {initialStore finalStore : Store} {value : Value}
    (evaluation : Evaluates (leading ++ suffix) initialStore expr value finalStore) :
    ∃ cost, ∀ continuation,
      Steps cost
        ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ ∧
      Steps cost
        ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix),
          continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩ := by
  induction fragment generalizing leading initialStore finalStore value with
  | unit =>
      cases evaluation
      simp only [Expr.weakenAt]
      exact ⟨1, fun _ => ⟨.cons .unit .refl, .cons .unit .refl⟩⟩
  | bool =>
      cases evaluation
      simp only [Expr.weakenAt]
      exact ⟨1, fun _ => ⟨.cons .bool .refl, .cons .bool .refl⟩⟩
  | word =>
      cases evaluation
      simp only [Expr.weakenAt]
      exact ⟨1, fun _ => ⟨.cons .word .refl, .cons .word .refl⟩⟩
  | @var index =>
      cases evaluation with
      | var found =>
          refine ⟨1, fun continuation => ⟨.cons (.var found) .refl, ?_⟩⟩
          simp only [Expr.weakenAt]
          have positions := lookup_insert leading suffix inserted index
          by_cases shifted : leading.length ≤ index <;>
            simp only [shifted, ↓reduceIte] at positions ⊢
          all_goals exact .cons (.var (positions.trans found)) .refl
  | unary _ ih =>
      cases evaluation with
      | unary child applied =>
          obtain ⟨childCost, childPaths⟩ := ih leading child
          refine ⟨childCost + 2, fun continuation => ?_⟩
          constructor
          · exact unary_path (childPaths _).1 applied
          · simp only [Expr.weakenAt]
            exact unary_path (childPaths _).2 applied
  | binary _ _ leftIH rightIH =>
      cases evaluation with
      | binary left right applied =>
          obtain ⟨leftCost, leftPaths⟩ := leftIH leading left
          obtain ⟨rightCost, rightPaths⟩ := rightIH leading right
          refine ⟨leftCost + rightCost + 3, fun continuation => ?_⟩
          constructor
          · exact binary_path (leftPaths _).1 (rightPaths _).1 applied
          · simp only [Expr.weakenAt]
            exact binary_path (leftPaths _).2 (rightPaths _).2 applied
  | letE _ _ valueIH bodyIH =>
      cases evaluation with
      | @letE _ _ _ _ _ _ boundValue _ valueEvaluation bodyEvaluation =>
          obtain ⟨valueCost, valuePaths⟩ := valueIH leading valueEvaluation
          obtain ⟨bodyCost, bodyPaths⟩ := bodyIH (boundValue :: leading) bodyEvaluation
          refine ⟨valueCost + bodyCost + 2, fun continuation => ?_⟩
          constructor
          · exact let_path (valuePaths _).1 (bodyPaths _).1
          · simp only [Expr.weakenAt]
            exact let_path (valuePaths _).2 (bodyPaths _).2
  | ifE _ _ _ conditionIH thenIH elseIH =>
      cases evaluation with
      | ifTrue condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := conditionIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := thenIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact if_true_path (conditionPaths _).1 (branchPaths _).1
          · simp only [Expr.weakenAt]
            exact if_true_path (conditionPaths _).2 (branchPaths _).2
      | ifFalse condition branch =>
          obtain ⟨conditionCost, conditionPaths⟩ := conditionIH leading condition
          obtain ⟨branchCost, branchPaths⟩ := elseIH leading branch
          refine ⟨conditionCost + branchCost + 2, fun continuation => ?_⟩
          constructor
          · exact if_false_path (conditionPaths _).1 (branchPaths _).1
          · simp only [Expr.weakenAt]
            exact if_false_path (conditionPaths _).2 (branchPaths _).2

end Solcore.Core
