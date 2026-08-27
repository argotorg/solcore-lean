import Solcore.Core.DerivedComparisonFlags
import Solcore.Core.DerivedComparisonEval

set_option autoImplicit false

namespace Solcore.Core
namespace Evaluates

/-! Store-threaded evaluation interface for derived word comparison flags. -/

theorem wordNeFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNeFlag right)
      (.word (if !(leftValue == rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordNe rightEvaluation).boolToWord

theorem wordNeFlag_eq
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (equal : leftValue = rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNeFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordNe_eq equal leftEvaluation rightEvaluation).boolToWord_false

theorem wordNeFlag_ne
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (notEqual : leftValue ≠ rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordNeFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordNe_ne notEqual leftEvaluation rightEvaluation).boolToWord_true

theorem wordLeFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLeFlag right)
      (.word (if !(decide (leftValue > rightValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordLe rightEvaluation).boolToWord

theorem wordLeFlag_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (greater : leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLeFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordLe_gt greater leftEvaluation rightEvaluation).boolToWord_false

theorem wordLeFlag_not_gt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (notGreater : ¬ leftValue > rightValue)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordLeFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordLe_not_gt notGreater leftEvaluation rightEvaluation).boolToWord_true

theorem wordLtFlag
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordLtFlag right)
      (.word (if decide (rightValue > leftValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordLt rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordLtFlag_lt
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
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
    Evaluates environment initialStore (left.wordLtFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordLt_lt less leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_true

theorem wordLtFlag_not_lt
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
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
    Evaluates environment initialStore (left.wordLtFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordLt_not_lt notLess leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping).boolToWord_false

theorem wordGeFlag
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordGeFlag right)
      (.word (if !(decide (rightValue > leftValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordGe rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordGeFlag_lt
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
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
    Evaluates environment initialStore (left.wordGeFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordGe_lt less leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_false

theorem wordGeFlag_not_lt
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
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
    Evaluates environment initialStore (left.wordGeFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordGe_not_lt notLess leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping).boolToWord_true

end Evaluates
end Solcore.Core
