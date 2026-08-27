import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value and evaluation interface for signed word greater-than. -/

namespace Word

@[simp] theorem signedGt_self (value : Word) :
    value.signedGt value = false := by
  by_cases nonnegative : value.val < 2 ^ 255
  · simp [signedGt, nonnegative]
  · simp [signedGt, nonnegative]

theorem signedGt_both_nonnegative
    (left right : Word)
    (leftNonnegative : left.val < 2 ^ 255)
    (rightNonnegative : right.val < 2 ^ 255) :
    left.signedGt right = decide (left > right) := by
  simp [signedGt, leftNonnegative, rightNonnegative]

theorem signedGt_both_negative
    (left right : Word)
    (leftNegative : 2 ^ 255 ≤ left.val)
    (rightNegative : 2 ^ 255 ≤ right.val) :
    left.signedGt right = decide (left > right) := by
  simp [signedGt, Nat.not_lt_of_ge leftNegative,
    Nat.not_lt_of_ge rightNegative]

@[simp] theorem signedGt_nonnegative_negative
    (left right : Word)
    (leftNonnegative : left.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ right.val) :
    left.signedGt right = true := by
  simp [signedGt, leftNonnegative, Nat.not_lt_of_ge rightNegative]

@[simp] theorem signedGt_negative_nonnegative
    (left right : Word)
    (leftNegative : 2 ^ 255 ≤ left.val)
    (rightNonnegative : right.val < 2 ^ 255) :
    left.signedGt right = false := by
  simp [signedGt, Nat.not_lt_of_ge leftNegative, rightNonnegative]

end Word

namespace BinaryOp

@[simp] theorem apply_wordSgt (left right : Word) :
    BinaryOp.wordSgt.apply (.word left) (.word right) =
      some (.bool (left.signedGt right)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordSgt
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordSgt left right)
      (.bool (leftValue.signedGt rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordSgt_both_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordSgt left right)
      (.bool (decide (leftValue > rightValue))) finalStore := by
  simpa only [Word.signedGt_both_nonnegative
    leftValue rightValue leftNonnegative rightNonnegative] using
    leftEvaluation.wordSgt rightEvaluation

theorem wordSgt_both_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordSgt left right)
      (.bool (decide (leftValue > rightValue))) finalStore := by
  simpa only [Word.signedGt_both_negative
    leftValue rightValue leftNegative rightNegative] using
    leftEvaluation.wordSgt rightEvaluation

theorem wordSgt_nonnegative_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNonnegative : leftValue.val < 2 ^ 255)
    (rightNegative : 2 ^ 255 ≤ rightValue.val)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordSgt left right)
      (.bool true) finalStore := by
  simpa only [Word.signedGt_nonnegative_negative
    leftValue rightValue leftNonnegative rightNegative] using
    leftEvaluation.wordSgt rightEvaluation

theorem wordSgt_negative_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftNegative : 2 ^ 255 ≤ leftValue.val)
    (rightNonnegative : rightValue.val < 2 ^ 255)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordSgt left right)
      (.bool false) finalStore := by
  simpa only [Word.signedGt_negative_nonnegative
    leftValue rightValue leftNegative rightNonnegative] using
    leftEvaluation.wordSgt rightEvaluation

end Evaluates

end Solcore.Core
