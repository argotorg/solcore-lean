import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused application and evaluation interface for direct word comparisons. -/

namespace BinaryOp

@[simp] theorem apply_wordEq (left right : Word) :
    BinaryOp.wordEq.apply (.word left) (.word right) =
      some (.bool (left == right)) := by
  rfl

@[simp] theorem apply_wordGt (left right : Word) :
    BinaryOp.wordGt.apply (.word left) (.word right) =
      some (.bool (decide (left > right))) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordEq
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordEq left right)
      (.bool (leftValue == rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordEq_eq
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (valuesEqual : leftValue = rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordEq left right)
      (.bool true) finalStore := by
  subst rightValue
  simpa using leftEvaluation.wordEq rightEvaluation

theorem wordEq_ne
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (valuesNotEqual : leftValue ≠ rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordEq left right)
      (.bool false) finalStore := by
  have valuesBeq : (leftValue == rightValue) = false :=
    beq_eq_false_iff_ne.mpr valuesNotEqual
  simpa [valuesBeq] using leftEvaluation.wordEq rightEvaluation

theorem wordGt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordGt left right)
      (.bool (decide (leftValue > rightValue))) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordGt_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (greater : leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordGt left right)
      (.bool true) finalStore := by
  simpa [greater] using leftEvaluation.wordGt rightEvaluation

theorem wordGt_not_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (notGreater : ¬ leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordGt left right)
      (.bool false) finalStore := by
  simpa [notGreater] using leftEvaluation.wordGt rightEvaluation

end Evaluates

end Solcore.Core
