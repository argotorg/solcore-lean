import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value and evaluation interface for word byte selection. -/

namespace Word

theorem byteAt_of_lt_32
    (index value : Word) (small : index.val < 32) :
    index.byteAt value =
      Word.ofNatModulo
        ((value.val / 2 ^ (8 * (31 - index.val))) % 256) := by
  simp [byteAt, small]

@[simp] theorem byteAt_of_ge_32
    (index value : Word) (large : 32 ≤ index.val) :
    index.byteAt value = Word.zero := by
  simp [byteAt, Nat.not_lt_of_ge large]

@[simp] theorem byteAt_zero (index : Word) :
    index.byteAt Word.zero = Word.zero := by
  by_cases small : index.val < 32
  · apply Fin.ext
    simp [byteAt, small, Word.zero, Word.ofNatModulo]
  · simp [byteAt, small]

@[simp] theorem byteAt_index30_1122 :
    (Word.ofNatModulo 30).byteAt (Word.ofNatModulo 0x1122) =
      Word.ofNatModulo 0x11 := by
  rfl

@[simp] theorem byteAt_index31_1122 :
    (Word.ofNatModulo 31).byteAt (Word.ofNatModulo 0x1122) =
      Word.ofNatModulo 0x22 := by
  rfl

end Word

namespace BinaryOp

@[simp] theorem apply_wordByte (index value : Word) :
    BinaryOp.wordByte.apply (.word index) (.word value) =
      some (.word (index.byteAt value)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordByte
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {index value : Expr} {indexResult valueResult : Word}
    (indexEvaluation :
      Evaluates environment initialStore index (.word indexResult) intermediateStore)
    (valueEvaluation :
      Evaluates environment intermediateStore value (.word valueResult) finalStore) :
    Evaluates environment initialStore (.binary .wordByte index value)
      (.word (indexResult.byteAt valueResult)) finalStore :=
  .binary indexEvaluation valueEvaluation rfl

theorem wordByte_lt_32
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {index value : Expr} {indexResult valueResult : Word}
    (small : indexResult.val < 32)
    (indexEvaluation :
      Evaluates environment initialStore index (.word indexResult) intermediateStore)
    (valueEvaluation :
      Evaluates environment intermediateStore value (.word valueResult) finalStore) :
    Evaluates environment initialStore (.binary .wordByte index value)
      (.word (Word.ofNatModulo
        ((valueResult.val / 2 ^ (8 * (31 - indexResult.val))) % 256)))
      finalStore := by
  simpa [Word.byteAt_of_lt_32 indexResult valueResult small] using
    indexEvaluation.wordByte valueEvaluation

theorem wordByte_ge_32
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {index value : Expr} {indexResult valueResult : Word}
    (large : 32 ≤ indexResult.val)
    (indexEvaluation :
      Evaluates environment initialStore index (.word indexResult) intermediateStore)
    (valueEvaluation :
      Evaluates environment intermediateStore value (.word valueResult) finalStore) :
    Evaluates environment initialStore (.binary .wordByte index value)
      (.word Word.zero) finalStore := by
  simpa [Word.byteAt_of_ge_32 indexResult valueResult large] using
    indexEvaluation.wordByte valueEvaluation

end Evaluates

end Solcore.Core
