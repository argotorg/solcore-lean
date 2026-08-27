import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value and evaluation interface for binary bitwise word logic. -/

namespace Word

@[simp] theorem bitAnd_zero (value : Word) :
    value.bitAnd Word.zero = Word.zero := by
  apply Fin.ext
  simp [bitAnd, Word.zero]

@[simp] theorem bitAnd_self (value : Word) :
    value.bitAnd value = value := by
  apply Fin.ext
  simp [bitAnd]

theorem bitAnd_comm (left right : Word) :
    left.bitAnd right = right.bitAnd left := by
  apply Fin.ext
  simp [bitAnd, Nat.and_comm]

@[simp] theorem bitOr_zero (value : Word) :
    value.bitOr Word.zero = value := by
  apply Fin.ext
  change (value.val ||| 0) % wordModulus = value.val
  simp [Nat.mod_eq_of_lt value.isLt]

@[simp] theorem bitOr_self (value : Word) :
    value.bitOr value = value := by
  apply Fin.ext
  change (value.val ||| value.val) % wordModulus = value.val
  simp [Nat.mod_eq_of_lt value.isLt]

theorem bitOr_comm (left right : Word) :
    left.bitOr right = right.bitOr left := by
  apply Fin.ext
  change (left.val ||| right.val) % wordModulus =
    (right.val ||| left.val) % wordModulus
  rw [Nat.or_comm]

@[simp] theorem bitXor_zero (value : Word) :
    value.bitXor Word.zero = value := by
  apply Fin.ext
  change (value.val ^^^ 0) % wordModulus = value.val
  simp [Nat.mod_eq_of_lt value.isLt]

@[simp] theorem bitXor_self (value : Word) :
    value.bitXor value = Word.zero := by
  apply Fin.ext
  change (value.val ^^^ value.val) % wordModulus = 0
  simp

theorem bitXor_comm (left right : Word) :
    left.bitXor right = right.bitXor left := by
  apply Fin.ext
  change (left.val ^^^ right.val) % wordModulus =
    (right.val ^^^ left.val) % wordModulus
  rw [Nat.xor_comm]

end Word

namespace BinaryOp

@[simp] theorem apply_wordAnd (left right : Word) :
    BinaryOp.wordAnd.apply (.word left) (.word right) =
      some (.word (left.bitAnd right)) := by
  rfl

@[simp] theorem apply_wordOr (left right : Word) :
    BinaryOp.wordOr.apply (.word left) (.word right) =
      some (.word (left.bitOr right)) := by
  rfl

@[simp] theorem apply_wordXor (left right : Word) :
    BinaryOp.wordXor.apply (.word left) (.word right) =
      some (.word (left.bitXor right)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordAnd
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordAnd left right)
      (.word (leftValue.bitAnd rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordOr
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordOr left right)
      (.word (leftValue.bitOr rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordXor
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordXor left right)
      (.word (leftValue.bitXor rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

end Evaluates

end Solcore.Core
