import Solcore.Core.DerivedSignedNonStrictComparisonFlags
import Solcore.Core.DerivedSignedNonStrictComparisonEval

set_option autoImplicit false

namespace Solcore.Core
namespace Evaluates

/-! Store-threaded evaluation interface for signed non-strict word flags. -/

theorem wordSleFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word (if !(leftValue.signedGt rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordSle rightEvaluation).boolToWord

theorem wordSleFlag_both_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word (if !(decide (leftValue > rightValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSle_both_nonnegative leftNonnegative rightNonnegative
    leftEvaluation rightEvaluation).boolToWord

theorem wordSleFlag_both_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word (if !(decide (leftValue > rightValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSle_both_negative leftNegative rightNegative
    leftEvaluation rightEvaluation).boolToWord

theorem wordSleFlag_nonnegative_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordSle_nonnegative_negative leftNonnegative rightNegative
    leftEvaluation rightEvaluation).boolToWord_false

theorem wordSleFlag_negative_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSleFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordSle_negative_nonnegative leftNegative rightNonnegative
    leftEvaluation rightEvaluation).boolToWord_true

theorem wordSgeFlag
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
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word (if !(rightValue.signedGt leftValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordSge rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSgeFlag_both_nonnegative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word (if !(decide (rightValue > leftValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSge_both_nonnegative leftNonnegative rightNonnegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSgeFlag_both_negative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word (if !(decide (rightValue > leftValue)) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSge_both_negative leftNegative rightNegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSgeFlag_nonnegative_negative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordSge_nonnegative_negative leftNonnegative rightNegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_true

theorem wordSgeFlag_negative_nonnegative
    {definitions : DataEnvironment} {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store} {world : StoreTyping}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore)
    (leftTyping : HasType context left .word definitions)
    (rightTyping : HasType context right .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore) :
    Evaluates environment initialStore (left.wordSgeFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordSge_negative_nonnegative leftNegative rightNonnegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_false

end Evaluates
end Solcore.Core
