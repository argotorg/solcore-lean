import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value, application, and evaluation interface for word sign extension. -/

namespace Word

theorem signExtend_clear
    (index value : Word)
    (small : index.val < 32)
    (clear :
      value.val % 2 ^ (8 * (index.val + 1)) <
        2 ^ (8 * (index.val + 1) - 1)) :
    index.signExtend value =
      Word.ofNatModulo (value.val % 2 ^ (8 * (index.val + 1))) := by
  simp [signExtend, small, clear]

theorem signExtend_set
    (index value : Word)
    (small : index.val < 32)
    (set :
      2 ^ (8 * (index.val + 1) - 1) ≤
        value.val % 2 ^ (8 * (index.val + 1))) :
    index.signExtend value =
      Word.ofNatModulo
        (wordModulus - 2 ^ (8 * (index.val + 1)) +
          value.val % 2 ^ (8 * (index.val + 1))) := by
  simp [signExtend, small, Nat.not_lt_of_ge set]

@[simp] theorem signExtend_ge_32
    (index value : Word) (large : 32 ≤ index.val) :
    index.signExtend value = value := by
  simp [signExtend, Nat.not_lt_of_ge large]

@[simp] theorem signExtend_zero (index : Word) :
    index.signExtend Word.zero = Word.zero := by
  by_cases small : index.val < 32
  · have signPositive :
        0 < 2 ^ (8 * (index.val + 1) - 1) :=
      Nat.two_pow_pos _
    apply Fin.ext
    simp [signExtend, small, signPositive, Word.zero, Word.ofNatModulo]
  · simp [signExtend, small]

@[simp] theorem signExtend_index31 (value : Word) :
    (Word.ofNatModulo 31).signExtend value = value := by
  have indexValue : (Word.ofNatModulo 31).val = 31 := by
    decide
  have small : (Word.ofNatModulo 31).val < 32 := by
    decide
  have width :
      2 ^ (8 * ((Word.ofNatModulo 31).val + 1)) = wordModulus := by
    simp [indexValue, wordModulus]
  have low :
      value.val % 2 ^ (8 * ((Word.ofNatModulo 31).val + 1)) = value.val := by
    rw [width]
    exact Nat.mod_eq_of_lt value.isLt
  have ofValue : Word.ofNatModulo value.val = value := by
    apply Fin.ext
    simp [Word.ofNatModulo, Nat.mod_eq_of_lt value.isLt]
  by_cases clear : value.val < 2 ^ 255
  · have clearBranch :
        value.val % 2 ^ (8 * ((Word.ofNatModulo 31).val + 1)) <
          2 ^ (8 * ((Word.ofNatModulo 31).val + 1) - 1) := by
      rw [low]
      simpa [indexValue] using clear
    rw [signExtend_clear _ _ small clearBranch, low, ofValue]
  · have setBranch :
        2 ^ (8 * ((Word.ofNatModulo 31).val + 1) - 1) ≤
          value.val % 2 ^ (8 * ((Word.ofNatModulo 31).val + 1)) := by
      rw [low]
      simpa [indexValue] using Nat.le_of_not_gt clear
    rw [signExtend_set _ _ small setBranch, low, width]
    simpa using ofValue

end Word

namespace BinaryOp

@[simp] theorem apply_wordSignExtend (index value : Word) :
    BinaryOp.wordSignExtend.apply (.word index) (.word value) =
      some (.word (index.signExtend value)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordSignExtend
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {index value : Expr} {indexResult valueResult : Word}
    (indexEvaluation :
      Evaluates environment initialStore index (.word indexResult) intermediateStore)
    (valueEvaluation :
      Evaluates environment intermediateStore value (.word valueResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSignExtend index value)
      (.word (indexResult.signExtend valueResult)) finalStore :=
  .binary indexEvaluation valueEvaluation rfl

theorem wordSignExtend_clear
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {index value : Expr} {indexResult valueResult : Word}
    (small : indexResult.val < 32)
    (clear :
      valueResult.val % 2 ^ (8 * (indexResult.val + 1)) <
        2 ^ (8 * (indexResult.val + 1) - 1))
    (indexEvaluation :
      Evaluates environment initialStore index (.word indexResult) intermediateStore)
    (valueEvaluation :
      Evaluates environment intermediateStore value (.word valueResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSignExtend index value)
      (.word (Word.ofNatModulo
        (valueResult.val % 2 ^ (8 * (indexResult.val + 1))))) finalStore := by
  simpa [Word.signExtend_clear indexResult valueResult small clear] using
    indexEvaluation.wordSignExtend valueEvaluation

theorem wordSignExtend_set
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {index value : Expr} {indexResult valueResult : Word}
    (small : indexResult.val < 32)
    (set :
      2 ^ (8 * (indexResult.val + 1) - 1) ≤
        valueResult.val % 2 ^ (8 * (indexResult.val + 1)))
    (indexEvaluation :
      Evaluates environment initialStore index (.word indexResult) intermediateStore)
    (valueEvaluation :
      Evaluates environment intermediateStore value (.word valueResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSignExtend index value)
      (.word (Word.ofNatModulo
        (wordModulus - 2 ^ (8 * (indexResult.val + 1)) +
          valueResult.val % 2 ^ (8 * (indexResult.val + 1))))) finalStore := by
  simpa [Word.signExtend_set indexResult valueResult small set] using
    indexEvaluation.wordSignExtend valueEvaluation

theorem wordSignExtend_ge_32
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {index value : Expr} {indexResult valueResult : Word}
    (large : 32 ≤ indexResult.val)
    (indexEvaluation :
      Evaluates environment initialStore index (.word indexResult) intermediateStore)
    (valueEvaluation :
      Evaluates environment intermediateStore value (.word valueResult) finalStore) :
    Evaluates environment initialStore (.binary .wordSignExtend index value)
      (.word valueResult) finalStore := by
  simpa [Word.signExtend_ge_32 indexResult valueResult large] using
    indexEvaluation.wordSignExtend valueEvaluation

end Evaluates

end Solcore.Core
