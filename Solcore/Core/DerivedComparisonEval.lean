import Solcore.Core.DerivedComparisons
import Solcore.Core.DirectWordComparisons
import Solcore.Core.RenamingInsertion

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
  .unary (leftEvaluation.wordEq rightEvaluation) rfl

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
  .unary (leftEvaluation.wordGt rightEvaluation) rfl

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

theorem wordLt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLt right)
      (.bool (decide (rightValue > leftValue))) finalStore := by
  obtain ⟨intermediateWorld, extension, intermediateStoreTyping, _⟩ :=
    evaluation_preserves_type leftEvaluation leftTyping
      environmentTyping storeTyping
  have shiftedRightEvaluation :=
    rightEvaluation.weakenAt_zero_word rightTyping
      (environmentTyping.weaken extension) intermediateStoreTyping
      (.word leftValue)
  rw [Expr.wordLt_expansion]
  apply Evaluates.letE leftEvaluation
  apply Evaluates.letE shiftedRightEvaluation
  have rightVariable :
      Evaluates (.word rightValue :: .word leftValue :: environment)
        finalStore (.var 0) (.word rightValue) finalStore :=
    .var (by simp)
  have leftVariable :
      Evaluates (.word rightValue :: .word leftValue :: environment)
        finalStore (.var 1) (.word leftValue) finalStore :=
    .var (by simp)
  exact rightVariable.wordGt leftVariable

theorem wordGe
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGe right)
      (.bool (!(decide (rightValue > leftValue)))) finalStore := by
  change Evaluates environment initialStore
    (.unary .boolNot (left.wordLt right)) _ finalStore
  exact .unary
    (leftEvaluation.wordLt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping) rfl

theorem wordLt_lt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (less : leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLt right)
      (.bool true) finalStore := by
  simpa [less] using leftEvaluation.wordLt rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping

theorem wordLt_not_lt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (notLess : ¬ leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLt right)
      (.bool false) finalStore := by
  simpa [notLess] using leftEvaluation.wordLt rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping

theorem wordGe_lt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (less : leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGe right)
      (.bool false) finalStore := by
  simpa [less] using leftEvaluation.wordGe rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping

theorem wordGe_not_lt
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
    (notLess : ¬ leftValue < rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGe right)
      (.bool true) finalStore := by
  simpa [notLess] using leftEvaluation.wordGe rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping

end Evaluates

end Solcore.Core
