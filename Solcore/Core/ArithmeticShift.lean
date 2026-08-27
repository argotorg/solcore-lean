import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value and evaluation interface for arithmetic word right shift. -/

namespace Word

@[simp] theorem shiftArithmeticRight_zero (value : Word) :
    value.shiftArithmeticRight Word.zero = value := by
  by_cases nonnegative : value.val < 2 ^ 255
  · apply Fin.ext
    simp [shiftArithmeticRight, Word.zero, nonnegative, Word.ofNatModulo,
      Nat.mod_eq_of_lt value.isLt]
  · have valueLe : value.val ≤ wordModulus - 1 :=
      Nat.le_sub_one_of_lt value.isLt
    apply Fin.ext
    simp [shiftArithmeticRight, Word.zero, nonnegative, Word.ofNatModulo,
      Nat.sub_sub_self valueLe, Nat.mod_eq_of_lt value.isLt]

theorem shiftArithmeticRight_of_lt_256_nonnegative
    (value shift : Word)
    (small : shift.val < 256)
    (nonnegative : value.val < 2 ^ 255) :
    value.shiftArithmeticRight shift =
      Word.ofNatModulo (value.val / 2 ^ shift.val) := by
  simp [shiftArithmeticRight, small, nonnegative]

theorem shiftArithmeticRight_of_lt_256_negative
    (value shift : Word)
    (small : shift.val < 256)
    (negative : 2 ^ 255 ≤ value.val) :
    value.shiftArithmeticRight shift =
      Word.ofNatModulo
        (wordModulus - 1 -
          ((wordModulus - 1 - value.val) / 2 ^ shift.val)) := by
  simp [shiftArithmeticRight, small, Nat.not_lt_of_ge negative]

@[simp] theorem shiftArithmeticRight_of_ge_256_nonnegative
    (value shift : Word)
    (large : 256 ≤ shift.val)
    (nonnegative : value.val < 2 ^ 255) :
    value.shiftArithmeticRight shift = Word.zero := by
  simp [shiftArithmeticRight, Nat.not_lt_of_ge large, nonnegative]

@[simp] theorem shiftArithmeticRight_of_ge_256_negative
    (value shift : Word)
    (large : 256 ≤ shift.val)
    (negative : 2 ^ 255 ≤ value.val) :
    value.shiftArithmeticRight shift = Word.maximum := by
  simp [shiftArithmeticRight, Nat.not_lt_of_ge large,
    Nat.not_lt_of_ge negative]

end Word

namespace BinaryOp

@[simp] theorem apply_wordSar (value shift : Word) :
    BinaryOp.wordSar.apply (.word value) (.word shift) =
      some (.word (value.shiftArithmeticRight shift)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordSar
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSar value shift)
      (.word (valueResult.shiftArithmeticRight shiftResult)) finalStore :=
  .binary valueEvaluation shiftEvaluation rfl

theorem wordSar_lt_256_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (small : shiftResult.val < 256)
    (nonnegative : valueResult.val < 2 ^ 255)
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSar value shift)
      (.word (Word.ofNatModulo (valueResult.val / 2 ^ shiftResult.val)))
      finalStore := by
  simpa [Word.shiftArithmeticRight_of_lt_256_nonnegative
    valueResult shiftResult small nonnegative] using
    valueEvaluation.wordSar shiftEvaluation

theorem wordSar_lt_256_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (small : shiftResult.val < 256)
    (negative : 2 ^ 255 ≤ valueResult.val)
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSar value shift)
      (.word (Word.ofNatModulo
        (wordModulus - 1 -
          ((wordModulus - 1 - valueResult.val) / 2 ^ shiftResult.val))))
      finalStore := by
  simpa [Word.shiftArithmeticRight_of_lt_256_negative
    valueResult shiftResult small negative] using
    valueEvaluation.wordSar shiftEvaluation

theorem wordSar_ge_256_nonnegative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (large : 256 ≤ shiftResult.val)
    (nonnegative : valueResult.val < 2 ^ 255)
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSar value shift)
      (.word Word.zero) finalStore := by
  simpa [Word.shiftArithmeticRight_of_ge_256_nonnegative
    valueResult shiftResult large nonnegative] using
    valueEvaluation.wordSar shiftEvaluation

theorem wordSar_ge_256_negative
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (large : 256 ≤ shiftResult.val)
    (negative : 2 ^ 255 ≤ valueResult.val)
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSar value shift)
      (.word Word.maximum) finalStore := by
  simpa [Word.shiftArithmeticRight_of_ge_256_negative
    valueResult shiftResult large negative] using
    valueEvaluation.wordSar shiftEvaluation

end Evaluates

end Solcore.Core
