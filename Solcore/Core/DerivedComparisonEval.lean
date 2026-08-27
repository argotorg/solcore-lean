import Solcore.Core.DerivedComparisons
import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Store-threaded evaluation interface for the non-swapping comparisons. -/

namespace Evaluates

theorem wordNe
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNe right)
      (.bool (!(leftValue == rightValue))) finalStore :=
  .unary (.binary leftEvaluation rightEvaluation rfl) rfl

theorem wordNe_eq
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (valuesEqual : leftValue = rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNe right)
      (.bool false) finalStore := by
  subst rightValue
  simpa using leftEvaluation.wordNe rightEvaluation

theorem wordNe_ne
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (valuesNotEqual : leftValue ≠ rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNe right)
      (.bool true) finalStore := by
  have valuesBeq : (leftValue == rightValue) = false :=
    beq_eq_false_iff_ne.mpr valuesNotEqual
  simpa [valuesBeq] using leftEvaluation.wordNe rightEvaluation

theorem wordLe
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLe right)
      (.bool (!(decide (leftValue > rightValue)))) finalStore :=
  .unary (.binary leftEvaluation rightEvaluation rfl) rfl

theorem wordLe_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (greater : leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLe right)
      (.bool false) finalStore := by
  simpa [greater] using leftEvaluation.wordLe rightEvaluation

theorem wordLe_not_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (notGreater : ¬ leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLe right)
      (.bool true) finalStore := by
  simpa [notGreater] using leftEvaluation.wordLe rightEvaluation

end Evaluates

end Solcore.Core
