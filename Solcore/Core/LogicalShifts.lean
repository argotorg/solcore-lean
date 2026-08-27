import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value and evaluation interface for bounded logical word shifts. -/

namespace Word

@[simp] theorem shiftLeft_zero (value : Word) :
    value.shiftLeft Word.zero = value := by
  apply Fin.ext
  simp [shiftLeft, Word.zero, Nat.mod_eq_of_lt value.isLt]

@[simp] theorem shiftRight_zero (value : Word) :
    value.shiftRight Word.zero = value := by
  apply Fin.ext
  simp [shiftRight, Word.zero]

theorem shiftLeft_of_lt_256
    (value shift : Word) (small : shift.val < 256) :
    value.shiftLeft shift = value <<< shift := by
  simp [shiftLeft, small]

theorem shiftRight_of_lt_256
    (value shift : Word) (small : shift.val < 256) :
    value.shiftRight shift = value >>> shift := by
  simp [shiftRight, small]

@[simp] theorem shiftLeft_of_ge_256
    (value shift : Word) (large : 256 ≤ shift.val) :
    value.shiftLeft shift = Word.zero := by
  simp [shiftLeft, Nat.not_lt_of_ge large]

@[simp] theorem shiftRight_of_ge_256
    (value shift : Word) (large : 256 ≤ shift.val) :
    value.shiftRight shift = Word.zero := by
  simp [shiftRight, Nat.not_lt_of_ge large]

end Word

namespace BinaryOp

@[simp] theorem apply_wordShl (value shift : Word) :
    BinaryOp.wordShl.apply (.word value) (.word shift) =
      some (.word (value.shiftLeft shift)) := by
  rfl

@[simp] theorem apply_wordShr (value shift : Word) :
    BinaryOp.wordShr.apply (.word value) (.word shift) =
      some (.word (value.shiftRight shift)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordShl
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordShl value shift)
      (.word (valueResult.shiftLeft shiftResult)) finalStore :=
  .binary valueEvaluation shiftEvaluation rfl

theorem wordShl_lt_256
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (small : shiftResult.val < 256)
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordShl value shift)
      (.word (valueResult <<< shiftResult)) finalStore := by
  simpa [Word.shiftLeft_of_lt_256 valueResult shiftResult small] using
    valueEvaluation.wordShl shiftEvaluation

theorem wordShl_ge_256
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (large : 256 ≤ shiftResult.val)
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordShl value shift)
      (.word Word.zero) finalStore := by
  simpa [Word.shiftLeft_of_ge_256 valueResult shiftResult large] using
    valueEvaluation.wordShl shiftEvaluation

theorem wordShr
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordShr value shift)
      (.word (valueResult.shiftRight shiftResult)) finalStore :=
  .binary valueEvaluation shiftEvaluation rfl

theorem wordShr_lt_256
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (small : shiftResult.val < 256)
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordShr value shift)
      (.word (valueResult >>> shiftResult)) finalStore := by
  simpa [Word.shiftRight_of_lt_256 valueResult shiftResult small] using
    valueEvaluation.wordShr shiftEvaluation

theorem wordShr_ge_256
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {value shift : Expr} {valueResult shiftResult : Word}
    (large : 256 ≤ shiftResult.val)
    (valueEvaluation :
      Evaluates environment initialStore value (.word valueResult) intermediateStore)
    (shiftEvaluation :
      Evaluates environment intermediateStore shift (.word shiftResult) finalStore) :
    Evaluates environment initialStore (.binary .wordShr value shift)
      (.word Word.zero) finalStore := by
  simpa [Word.shiftRight_of_ge_256 valueResult shiftResult large] using
    valueEvaluation.wordShr shiftEvaluation

end Evaluates

end Solcore.Core
