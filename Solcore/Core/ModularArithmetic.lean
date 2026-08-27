import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value and evaluation interface for modular word arithmetic. -/

namespace Word

@[simp] theorem add_zero (value : Word) :
    value.add Word.zero = value := by
  change value + Word.zero = value
  apply Fin.ext
  change (value.val + 0) % wordModulus = value.val
  exact Nat.mod_eq_of_lt value.isLt

@[simp] theorem add_maximum_one :
    Word.maximum.add (Word.ofNatModulo 1) = Word.zero := by
  rfl

@[simp] theorem sub_zero (value : Word) :
    value.sub Word.zero = value := by
  change value - Word.zero = value
  apply Fin.ext
  have zeroLe : Word.zero ≤ value := Nat.zero_le value.val
  rw [Fin.sub_val_of_le zeroLe]
  simp [Word.zero]

@[simp] theorem sub_self (value : Word) :
    value.sub value = Word.zero := by
  change value - value = Word.zero
  apply Fin.ext
  rw [Fin.sub_val_of_le (Fin.le_refl value)]
  simp [Word.zero]

@[simp] theorem zero_sub_one :
    Word.zero.sub (Word.ofNatModulo 1) = Word.maximum := by
  rfl

@[simp] theorem mul_zero (value : Word) :
    value.mul Word.zero = Word.zero := by
  change value * Word.zero = Word.zero
  apply Fin.ext
  change (value.val * 0) % wordModulus = 0
  simp

@[simp] theorem mul_one (value : Word) :
    value.mul (Word.ofNatModulo 1) = value := by
  change value * Word.ofNatModulo 1 = value
  apply Fin.ext
  change (value.val * (1 % wordModulus)) % wordModulus = value.val
  have oneLt : 1 < wordModulus := by decide
  rw [Nat.mod_eq_of_lt oneLt]
  simp [Nat.mod_eq_of_lt value.isLt]

@[simp] theorem maximum_mul_two :
    Word.maximum.mul (Word.ofNatModulo 2) =
      Word.ofNatModulo (wordModulus - 2) := by
  rfl

end Word

namespace BinaryOp

@[simp] theorem apply_wordAdd (left right : Word) :
    BinaryOp.wordAdd.apply (.word left) (.word right) =
      some (.word (left.add right)) := by
  rfl

@[simp] theorem apply_wordSub (left right : Word) :
    BinaryOp.wordSub.apply (.word left) (.word right) =
      some (.word (left.sub right)) := by
  rfl

@[simp] theorem apply_wordMul (left right : Word) :
    BinaryOp.wordMul.apply (.word left) (.word right) =
      some (.word (left.mul right)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordAdd
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordAdd left right)
      (.word (leftValue.add rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordSub
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordSub left right)
      (.word (leftValue.sub rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordMul
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordMul left right)
      (.word (leftValue.mul rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

end Evaluates

end Solcore.Core
