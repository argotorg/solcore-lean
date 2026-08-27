import Solcore.Core.DerivedSignedNonStrictComparisons
import Solcore.Core.DerivedSignedComparisonEval

set_option autoImplicit false

namespace Solcore.Core
namespace Evaluates

/-! Store-threaded evaluation interface for signed non-strict comparisons. -/

theorem wordSle
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool (!(leftValue.signedGt rightValue))) finalStore :=
  .unary (leftEvaluation.wordSgt rightEvaluation) rfl

theorem wordSle_both_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool (!(decide (leftValue > rightValue)))) finalStore :=
  .unary (Evaluates.wordSgt_both_nonnegative
    leftNonnegative rightNonnegative leftEvaluation rightEvaluation) rfl

theorem wordSle_both_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool (!(decide (leftValue > rightValue)))) finalStore :=
  .unary (Evaluates.wordSgt_both_negative
    leftNegative rightNegative leftEvaluation rightEvaluation) rfl

theorem wordSle_nonnegative_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool false) finalStore :=
  .unary (Evaluates.wordSgt_nonnegative_negative
    leftNonnegative rightNegative leftEvaluation rightEvaluation) rfl

theorem wordSle_negative_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSle right)
      (.bool true) finalStore :=
  .unary (Evaluates.wordSgt_negative_nonnegative
    leftNegative rightNonnegative leftEvaluation rightEvaluation) rfl

theorem wordSge
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
    Evaluates environment initialStore (left.wordSge right)
      (.bool (!(rightValue.signedGt leftValue))) finalStore :=
  .unary (leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping) rfl

theorem wordSge_both_nonnegative
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
    Evaluates environment initialStore (left.wordSge right)
      (.bool (!(decide (rightValue > leftValue)))) finalStore :=
  .unary (Evaluates.wordSlt_both_nonnegative
    leftNonnegative rightNonnegative leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping) rfl

theorem wordSge_both_negative
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
    Evaluates environment initialStore (left.wordSge right)
      (.bool (!(decide (rightValue > leftValue)))) finalStore :=
  .unary (Evaluates.wordSlt_both_negative
    leftNegative rightNegative leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping) rfl

theorem wordSge_nonnegative_negative
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
    Evaluates environment initialStore (left.wordSge right)
      (.bool true) finalStore :=
  .unary (Evaluates.wordSlt_nonnegative_negative
    leftNonnegative rightNegative leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping) rfl

theorem wordSge_negative_nonnegative
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
    Evaluates environment initialStore (left.wordSge right)
      (.bool false) finalStore :=
  .unary (Evaluates.wordSlt_negative_nonnegative
    leftNegative rightNonnegative leftEvaluation rightEvaluation
    leftTyping rightTyping environmentTyping storeTyping) rfl

end Evaluates
end Solcore.Core
