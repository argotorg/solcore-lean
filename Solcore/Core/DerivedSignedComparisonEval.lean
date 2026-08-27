import Solcore.Core.DerivedSignedComparisons
import Solcore.Core.SignedComparison
import Solcore.Core.RenamingInsertion

set_option autoImplicit false

namespace Solcore.Core

/-! Store-threaded evaluation interface for derived signed word less-than. -/

namespace Evaluates

theorem wordSlt
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
    Evaluates environment initialStore (left.wordSlt right)
      (.bool (rightValue.signedGt leftValue)) finalStore := by
  obtain ⟨intermediateWorld, extension, intermediateStoreTyping, _⟩ :=
    evaluation_preserves_type leftEvaluation leftTyping
      environmentTyping storeTyping
  have shiftedRightEvaluation :=
    rightEvaluation.weakenAt_zero_word rightTyping
      (environmentTyping.weaken extension) intermediateStoreTyping
      (.word leftValue)
  rw [Expr.wordSlt_expansion]
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
  exact rightVariable.wordSgt leftVariable

theorem wordSlt_both_nonnegative
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
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
    Evaluates environment initialStore (left.wordSlt right)
      (.bool (decide (rightValue > leftValue))) finalStore := by
  simpa only [Word.signedGt_both_nonnegative
    rightValue leftValue rightNonnegative leftNonnegative] using
    leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping

theorem wordSlt_both_negative
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
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
    Evaluates environment initialStore (left.wordSlt right)
      (.bool (decide (rightValue > leftValue))) finalStore := by
  simpa only [Word.signedGt_both_negative
    rightValue leftValue rightNegative leftNegative] using
    leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping

theorem wordSlt_nonnegative_negative
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
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
    Evaluates environment initialStore (left.wordSlt right)
      (.bool false) finalStore := by
  simpa only [Word.signedGt_negative_nonnegative
    rightValue leftValue rightNegative leftNonnegative] using
    leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping

theorem wordSlt_negative_nonnegative
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore intermediateStore finalStore : Store}
    {world : StoreTyping} {left right : Expr} {leftValue rightValue : Word}
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
    Evaluates environment initialStore (left.wordSlt right)
      (.bool true) finalStore := by
  simpa only [Word.signedGt_nonnegative_negative
    rightValue leftValue rightNonnegative leftNegative] using
    leftEvaluation.wordSlt rightEvaluation leftTyping rightTyping
      environmentTyping storeTyping

end Evaluates

end Solcore.Core
