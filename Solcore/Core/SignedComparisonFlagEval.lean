import Solcore.Core.SignedComparisonFlags
import Solcore.Core.SignedComparison
import Solcore.Core.DerivedSignedComparisonEval

set_option autoImplicit false

namespace Solcore.Core
namespace Evaluates

/-! Store-threaded evaluation interface for signed word comparison flags. -/

theorem wordSgtFlag
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word (if leftValue.signedGt rightValue then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordSgt rightEvaluation).boolToWord

theorem wordSgtFlag_both_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word (if decide (leftValue > rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSgt_both_nonnegative leftNonnegative rightNonnegative
    leftEvaluation rightEvaluation).boolToWord

theorem wordSgtFlag_both_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word (if decide (leftValue > rightValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSgt_both_negative leftNegative rightNegative
    leftEvaluation rightEvaluation).boolToWord

theorem wordSgtFlag_nonnegative_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordSgt_nonnegative_negative leftNonnegative rightNegative
    leftEvaluation rightEvaluation).boolToWord_true

theorem wordSgtFlag_negative_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (left.wordSgtFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordSgt_negative_nonnegative leftNegative rightNonnegative
    leftEvaluation rightEvaluation).boolToWord_false

theorem wordSltFlag
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
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word (if rightValue.signedGt leftValue then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSltFlag_both_nonnegative
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
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word (if decide (rightValue > leftValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSlt_both_nonnegative leftNonnegative rightNonnegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSltFlag_both_negative
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
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word (if decide (rightValue > leftValue) then
        Word.ofNatModulo 1 else Word.zero)) finalStore :=
  (Evaluates.wordSlt_both_negative leftNegative rightNegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord

theorem wordSltFlag_nonnegative_negative
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
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word Word.zero) finalStore :=
  (Evaluates.wordSlt_nonnegative_negative leftNonnegative rightNegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_false

theorem wordSltFlag_negative_nonnegative
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
    Evaluates environment initialStore (left.wordSltFlag right)
      (.word (Word.ofNatModulo 1)) finalStore :=
  (Evaluates.wordSlt_negative_nonnegative leftNegative rightNonnegative
    leftEvaluation rightEvaluation leftTyping rightTyping
    environmentTyping storeTyping).boolToWord_true

end Evaluates
end Solcore.Core
