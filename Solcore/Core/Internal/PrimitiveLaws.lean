import Solcore.Core.Internal.EvaluationLaws
import Solcore.Core.Internal.Renaming
import Solcore.Core.Primitive

/-!
# Laws of single primitives

Value, application and evaluation laws of the primitives, one section each. `WordComparisons`,
`ByteSelection` and `DerivedForms` hold the rest of this topic in files of their own: thousands of
modules reach those, and only tests and a few proofs import this one, so its simp lemmas stay out
of the others.
-/

section
-- leanmerge: from Solcore.Core.ArithmeticShift
/-! Focused value and evaluation interface for arithmetic word right shift. -/

set_option autoImplicit false

namespace Solcore.Core

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
end

section
-- leanmerge: from Solcore.Core.BitwiseLogic
/-! Focused value and evaluation interface for binary bitwise word logic. -/

set_option autoImplicit false

namespace Solcore.Core

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
end

section
-- leanmerge: from Solcore.Core.CountLeadingZeros
/-! Focused value and evaluation interface for word count-leading-zeros. -/

set_option autoImplicit false

namespace Solcore.Core

namespace Word

@[simp] theorem clz_zero :
    Word.zero.clz = Word.ofNatModulo 256 := by
  rfl

theorem clz_nonzero (value : Word) (nonzero : value.val ≠ 0) :
    value.clz = Word.ofNatModulo (255 - Nat.log2 value.val) := by
  simp [clz, nonzero]

@[simp] theorem clz_one :
    (Word.ofNatModulo 1).clz = Word.ofNatModulo 255 := by
  rfl

@[simp] theorem clz_highBit :
    (Word.ofNatModulo (2 ^ 255)).clz = Word.zero := by
  rfl

@[simp] theorem clz_maximum :
    Word.maximum.clz = Word.zero := by
  rfl

end Word

namespace UnaryOp

@[simp] theorem apply_wordClz (value : Word) :
    UnaryOp.wordClz.apply (.word value) = some (.word value.clz) := by
  rfl

end UnaryOp

namespace Evaluates

theorem wordClz
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word value.clz) finalStore :=
  .unary evaluation rfl

theorem wordClz_zero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word (Word.ofNatModulo 256)) finalStore := by
  simpa using evaluation.wordClz

theorem wordClz_one
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand
        (.word (Word.ofNatModulo 1)) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word (Word.ofNatModulo 255)) finalStore := by
  simpa using evaluation.wordClz

theorem wordClz_highBit
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand
        (.word (Word.ofNatModulo (2 ^ 255))) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word Word.zero) finalStore := by
  simpa only [Word.clz_highBit] using evaluation.wordClz

theorem wordClz_maximum
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.maximum) finalStore) :
    Evaluates environment initialStore (.unary .wordClz operand)
      (.word Word.zero) finalStore := by
  simpa using evaluation.wordClz

end Evaluates

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.LogicalShifts
/-! Focused value and evaluation interface for bounded logical word shifts. -/

set_option autoImplicit false

namespace Solcore.Core

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
end

section
-- leanmerge: from Solcore.Core.ModularArithmetic
/-! Focused value and evaluation interface for modular word arithmetic. -/

set_option autoImplicit false

namespace Solcore.Core

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
end

section
-- leanmerge: from Solcore.Core.ModularExponentiation
/-! Focused correctness and evaluation interface for modular word powers. -/

set_option autoImplicit false

namespace Solcore.Core

namespace Word

theorem modularPowLoop_correct (base accumulator exponent : Nat) :
    modularPowLoop base accumulator exponent =
      (accumulator * base ^ exponent) % wordModulus := by
  induction base, accumulator, exponent using modularPowLoop.induct with
  | case1 base accumulator =>
      rw [modularPowLoop]
      simp
  | case2 base accumulator exponent nonzero nextAccumulator inductionHypothesis =>
      rw [modularPowLoop]
      simp only [dif_neg nonzero]
      change modularPowLoop
        (base * base % wordModulus) nextAccumulator (exponent / 2) = _
      rw [inductionHypothesis]
      rcases Nat.mod_two_eq_zero_or_one exponent with even | odd
      · have exponentEquation : exponent = 2 * (exponent / 2) := by
          have division := Nat.mod_add_div exponent 2
          omega
        change
          (if exponent % 2 = 1 then
              accumulator * base % wordModulus
            else accumulator % wordModulus) *
              (base * base % wordModulus) ^ (exponent / 2) % wordModulus = _
        rw [if_neg (by omega)]
        conv =>
          rhs
          rw [exponentEquation, Nat.pow_mul]
          simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one]
        simp only [Nat.one_mul]
        simp [Nat.mul_mod, Nat.pow_mod]
      · have exponentEquation : exponent = 1 + 2 * (exponent / 2) := by
          have division := Nat.mod_add_div exponent 2
          omega
        change
          (if exponent % 2 = 1 then
              accumulator * base % wordModulus
            else accumulator % wordModulus) *
              (base * base % wordModulus) ^ (exponent / 2) % wordModulus = _
        rw [if_pos odd]
        conv =>
          rhs
          rw [exponentEquation, Nat.pow_add, Nat.pow_mul]
          simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
          rw [← Nat.mul_assoc]
        simp [Nat.mul_mod, Nat.pow_mod]

theorem pow_correct (base exponent : Word) :
    (base.pow exponent).val =
      base.val ^ exponent.val % wordModulus := by
  simp [pow, Word.ofNatModulo, modularPowLoop_correct]

@[simp] theorem pow_zero (base : Word) :
    base.pow Word.zero = Word.ofNatModulo 1 := by
  apply Fin.ext
  simp [pow_correct, Word.zero, Word.ofNatModulo]

@[simp] theorem pow_one (base : Word) :
    base.pow (Word.ofNatModulo 1) = base := by
  apply Fin.ext
  rw [pow_correct]
  have oneLt : 1 < wordModulus := by decide
  simp [Word.ofNatModulo, Nat.mod_eq_of_lt oneLt,
    Nat.mod_eq_of_lt base.isLt]

@[simp] theorem one_pow (exponent : Word) :
    (Word.ofNatModulo 1).pow exponent = Word.ofNatModulo 1 := by
  apply Fin.ext
  rw [pow_correct]
  have oneLt : 1 < wordModulus := by decide
  simp [Word.ofNatModulo, Nat.mod_eq_of_lt oneLt]

@[simp] theorem zero_pow_of_positive
    (exponent : Word) (positive : 0 < exponent.val) :
    Word.zero.pow exponent = Word.zero := by
  apply Fin.ext
  simp [pow_correct, Word.zero, positive]

@[simp] theorem two_pow_256 :
    (Word.ofNatModulo 2).pow (Word.ofNatModulo 256) = Word.zero := by
  apply Fin.ext
  rw [pow_correct]
  decide

@[simp] theorem maximum_pow_two :
    Word.maximum.pow (Word.ofNatModulo 2) = Word.ofNatModulo 1 := by
  apply Fin.ext
  rw [pow_correct]
  decide

end Word

namespace BinaryOp

@[simp] theorem apply_wordPow (base exponent : Word) :
    BinaryOp.wordPow.apply (.word base) (.word exponent) =
      some (.word (base.pow exponent)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordPow
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {base exponent : Expr} {baseResult exponentResult : Word}
    (baseEvaluation :
      Evaluates environment initialStore base (.word baseResult) intermediateStore)
    (exponentEvaluation :
      Evaluates environment intermediateStore exponent (.word exponentResult) finalStore) :
    Evaluates environment initialStore (.binary .wordPow base exponent)
      (.word (baseResult.pow exponentResult)) finalStore :=
  .binary baseEvaluation exponentEvaluation rfl

theorem wordPow_exponent_zero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {base exponent : Expr} {baseResult : Word}
    (baseEvaluation :
      Evaluates environment initialStore base (.word baseResult) intermediateStore)
    (exponentEvaluation :
      Evaluates environment intermediateStore exponent (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.binary .wordPow base exponent)
      (.word (Word.ofNatModulo 1)) finalStore := by
  simpa using baseEvaluation.wordPow exponentEvaluation

theorem wordPow_exponent_one
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {base exponent : Expr} {baseResult : Word}
    (baseEvaluation :
      Evaluates environment initialStore base (.word baseResult) intermediateStore)
    (exponentEvaluation :
      Evaluates environment intermediateStore exponent
        (.word (Word.ofNatModulo 1)) finalStore) :
    Evaluates environment initialStore (.binary .wordPow base exponent)
      (.word baseResult) finalStore := by
  simpa using baseEvaluation.wordPow exponentEvaluation

theorem wordPow_one_base
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {base exponent : Expr} {exponentResult : Word}
    (baseEvaluation :
      Evaluates environment initialStore base
        (.word (Word.ofNatModulo 1)) intermediateStore)
    (exponentEvaluation :
      Evaluates environment intermediateStore exponent
        (.word exponentResult) finalStore) :
    Evaluates environment initialStore (.binary .wordPow base exponent)
      (.word (Word.ofNatModulo 1)) finalStore := by
  simpa using baseEvaluation.wordPow exponentEvaluation

theorem wordPow_zero_base_of_positive
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {base exponent : Expr} {exponentResult : Word}
    (positive : 0 < exponentResult.val)
    (baseEvaluation :
      Evaluates environment initialStore base (.word Word.zero) intermediateStore)
    (exponentEvaluation :
      Evaluates environment intermediateStore exponent
        (.word exponentResult) finalStore) :
    Evaluates environment initialStore (.binary .wordPow base exponent)
      (.word Word.zero) finalStore := by
  simpa [Word.zero_pow_of_positive exponentResult positive] using
    baseEvaluation.wordPow exponentEvaluation

end Evaluates

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.SignExtension
/-! Focused value, application, and evaluation interface for word sign extension. -/

set_option autoImplicit false

namespace Solcore.Core

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
end

section
-- leanmerge: from Solcore.Core.SignedDivision
/-! Focused value, application, and evaluation interface for signed division and modulo. -/

set_option autoImplicit false

namespace Solcore.Core

namespace Word

@[simp] theorem sdiv_zero (dividend : Word) :
    dividend.sdiv Word.zero = Word.zero := by
  rfl

theorem sdiv_nonzero
    (dividend divisor : Word) (nonzero : divisor.val ≠ 0) :
    dividend.sdiv divisor =
      Word.ofSignedMagnitude
        (dividend.signedNegative != divisor.signedNegative)
        (dividend.signedMagnitude / divisor.signedMagnitude) := by
  simp [sdiv, nonzero]

@[simp] theorem smod_zero (dividend : Word) :
    dividend.smod Word.zero = Word.zero := by
  rfl

theorem smod_nonzero
    (dividend divisor : Word) (nonzero : divisor.val ≠ 0) :
    dividend.smod divisor =
      Word.ofSignedMagnitude dividend.signedNegative
        (dividend.signedMagnitude % divisor.signedMagnitude) := by
  simp [smod, nonzero]

@[simp] theorem sdiv_minimum_negative_one :
    (Word.ofNatModulo (2 ^ 255)).sdiv Word.maximum =
      Word.ofNatModulo (2 ^ 255) := by
  rfl

@[simp] theorem smod_minimum_negative_one :
    (Word.ofNatModulo (2 ^ 255)).smod Word.maximum = Word.zero := by
  rfl

end Word

namespace BinaryOp

@[simp] theorem apply_wordSdiv (dividend divisor : Word) :
    BinaryOp.wordSdiv.apply (.word dividend) (.word divisor) =
      some (.word (dividend.sdiv divisor)) := by
  rfl

@[simp] theorem apply_wordSmod (dividend divisor : Word) :
    BinaryOp.wordSmod.apply (.word dividend) (.word divisor) =
      some (.word (dividend.smod divisor)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordSdiv
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {dividend divisor : Expr} {dividendResult divisorResult : Word}
    (dividendEvaluation :
      Evaluates environment initialStore dividend (.word dividendResult)
        intermediateStore)
    (divisorEvaluation :
      Evaluates environment intermediateStore divisor (.word divisorResult)
        finalStore) :
    Evaluates environment initialStore (.binary .wordSdiv dividend divisor)
      (.word (dividendResult.sdiv divisorResult)) finalStore :=
  .binary dividendEvaluation divisorEvaluation rfl

theorem wordSdiv_zero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {dividend divisor : Expr} {dividendResult : Word}
    (dividendEvaluation :
      Evaluates environment initialStore dividend (.word dividendResult)
        intermediateStore)
    (divisorEvaluation :
      Evaluates environment intermediateStore divisor (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.binary .wordSdiv dividend divisor)
      (.word Word.zero) finalStore := by
  simpa using dividendEvaluation.wordSdiv divisorEvaluation

theorem wordSdiv_nonzero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {dividend divisor : Expr} {dividendResult divisorResult : Word}
    (nonzero : divisorResult.val ≠ 0)
    (dividendEvaluation :
      Evaluates environment initialStore dividend (.word dividendResult)
        intermediateStore)
    (divisorEvaluation :
      Evaluates environment intermediateStore divisor (.word divisorResult)
        finalStore) :
    Evaluates environment initialStore (.binary .wordSdiv dividend divisor)
      (.word (Word.ofSignedMagnitude
        (dividendResult.signedNegative != divisorResult.signedNegative)
        (dividendResult.signedMagnitude / divisorResult.signedMagnitude)))
      finalStore := by
  simpa only [Word.sdiv_nonzero dividendResult divisorResult nonzero] using
    dividendEvaluation.wordSdiv divisorEvaluation

theorem wordSmod
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {dividend divisor : Expr} {dividendResult divisorResult : Word}
    (dividendEvaluation :
      Evaluates environment initialStore dividend (.word dividendResult)
        intermediateStore)
    (divisorEvaluation :
      Evaluates environment intermediateStore divisor (.word divisorResult)
        finalStore) :
    Evaluates environment initialStore (.binary .wordSmod dividend divisor)
      (.word (dividendResult.smod divisorResult)) finalStore :=
  .binary dividendEvaluation divisorEvaluation rfl

theorem wordSmod_zero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {dividend divisor : Expr} {dividendResult : Word}
    (dividendEvaluation :
      Evaluates environment initialStore dividend (.word dividendResult)
        intermediateStore)
    (divisorEvaluation :
      Evaluates environment intermediateStore divisor (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.binary .wordSmod dividend divisor)
      (.word Word.zero) finalStore := by
  simpa using dividendEvaluation.wordSmod divisorEvaluation

theorem wordSmod_nonzero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {dividend divisor : Expr} {dividendResult divisorResult : Word}
    (nonzero : divisorResult.val ≠ 0)
    (dividendEvaluation :
      Evaluates environment initialStore dividend (.word dividendResult)
        intermediateStore)
    (divisorEvaluation :
      Evaluates environment intermediateStore divisor (.word divisorResult)
        finalStore) :
    Evaluates environment initialStore (.binary .wordSmod dividend divisor)
      (.word (Word.ofSignedMagnitude dividendResult.signedNegative
        (dividendResult.signedMagnitude % divisorResult.signedMagnitude)))
      finalStore := by
  simpa only [Word.smod_nonzero dividendResult divisorResult nonzero] using
    dividendEvaluation.wordSmod divisorEvaluation

end Evaluates

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.TernaryModularArithmetic
/-! Focused value, application, and evaluation interface for ternary modular arithmetic. -/

set_option autoImplicit false

namespace Solcore.Core

namespace Word

@[simp] theorem addMod_zero (left right : Word) :
    left.addMod right Word.zero = Word.zero := by
  rfl

theorem addMod_nonzero
    (left right modulus : Word) (nonzero : modulus.val ≠ 0) :
    left.addMod right modulus =
      Word.ofNatModulo ((left.val + right.val) % modulus.val) := by
  simp [addMod, nonzero]

@[simp] theorem mulMod_zero (left right : Word) :
    left.mulMod right Word.zero = Word.zero := by
  rfl

theorem mulMod_nonzero
    (left right modulus : Word) (nonzero : modulus.val ≠ 0) :
    left.mulMod right modulus =
      Word.ofNatModulo ((left.val * right.val) % modulus.val) := by
  simp [mulMod, nonzero]

@[simp] theorem addMod_no_prewrap :
    Word.maximum.addMod (Word.ofNatModulo 1) Word.maximum =
      Word.ofNatModulo 1 := by
  rfl

@[simp] theorem mulMod_no_prewrap :
    Word.maximum.mulMod Word.maximum Word.maximum = Word.zero := by
  rfl

end Word

namespace TernaryOp

@[simp] theorem apply_wordAddMod (left right modulus : Word) :
    TernaryOp.wordAddMod.apply (.word left) (.word right) (.word modulus) =
      some (.word (left.addMod right modulus)) := by
  rfl

@[simp] theorem apply_wordMulMod (left right modulus : Word) :
    TernaryOp.wordMulMod.apply (.word left) (.word right) (.word modulus) =
      some (.word (left.mulMod right modulus)) := by
  rfl

end TernaryOp

namespace Evaluates

theorem wordAddMod
    {environment : Environment}
    {initialStore afterFirstStore afterSecondStore finalStore : Store}
    {first second modulus : Expr}
    {firstResult secondResult modulusResult : Word}
    (firstEvaluation :
      Evaluates environment initialStore first (.word firstResult) afterFirstStore)
    (secondEvaluation :
      Evaluates environment afterFirstStore second (.word secondResult)
        afterSecondStore)
    (modulusEvaluation :
      Evaluates environment afterSecondStore modulus (.word modulusResult)
        finalStore) :
    Evaluates environment initialStore
      (.ternary .wordAddMod first second modulus)
      (.word (firstResult.addMod secondResult modulusResult)) finalStore :=
  .ternary firstEvaluation secondEvaluation modulusEvaluation rfl

theorem wordAddMod_zero
    {environment : Environment}
    {initialStore afterFirstStore afterSecondStore finalStore : Store}
    {first second modulus : Expr} {firstResult secondResult : Word}
    (firstEvaluation :
      Evaluates environment initialStore first (.word firstResult) afterFirstStore)
    (secondEvaluation :
      Evaluates environment afterFirstStore second (.word secondResult)
        afterSecondStore)
    (modulusEvaluation :
      Evaluates environment afterSecondStore modulus (.word Word.zero) finalStore) :
    Evaluates environment initialStore
      (.ternary .wordAddMod first second modulus) (.word Word.zero) finalStore := by
  simpa using firstEvaluation.wordAddMod secondEvaluation modulusEvaluation

theorem wordAddMod_nonzero
    {environment : Environment}
    {initialStore afterFirstStore afterSecondStore finalStore : Store}
    {first second modulus : Expr}
    {firstResult secondResult modulusResult : Word}
    (nonzero : modulusResult.val ≠ 0)
    (firstEvaluation :
      Evaluates environment initialStore first (.word firstResult) afterFirstStore)
    (secondEvaluation :
      Evaluates environment afterFirstStore second (.word secondResult)
        afterSecondStore)
    (modulusEvaluation :
      Evaluates environment afterSecondStore modulus (.word modulusResult)
        finalStore) :
    Evaluates environment initialStore
      (.ternary .wordAddMod first second modulus)
      (.word (Word.ofNatModulo
        ((firstResult.val + secondResult.val) % modulusResult.val))) finalStore := by
  simpa only [Word.addMod_nonzero firstResult secondResult modulusResult nonzero] using
    firstEvaluation.wordAddMod secondEvaluation modulusEvaluation

theorem wordMulMod
    {environment : Environment}
    {initialStore afterFirstStore afterSecondStore finalStore : Store}
    {first second modulus : Expr}
    {firstResult secondResult modulusResult : Word}
    (firstEvaluation :
      Evaluates environment initialStore first (.word firstResult) afterFirstStore)
    (secondEvaluation :
      Evaluates environment afterFirstStore second (.word secondResult)
        afterSecondStore)
    (modulusEvaluation :
      Evaluates environment afterSecondStore modulus (.word modulusResult)
        finalStore) :
    Evaluates environment initialStore
      (.ternary .wordMulMod first second modulus)
      (.word (firstResult.mulMod secondResult modulusResult)) finalStore :=
  .ternary firstEvaluation secondEvaluation modulusEvaluation rfl

theorem wordMulMod_zero
    {environment : Environment}
    {initialStore afterFirstStore afterSecondStore finalStore : Store}
    {first second modulus : Expr} {firstResult secondResult : Word}
    (firstEvaluation :
      Evaluates environment initialStore first (.word firstResult) afterFirstStore)
    (secondEvaluation :
      Evaluates environment afterFirstStore second (.word secondResult)
        afterSecondStore)
    (modulusEvaluation :
      Evaluates environment afterSecondStore modulus (.word Word.zero) finalStore) :
    Evaluates environment initialStore
      (.ternary .wordMulMod first second modulus) (.word Word.zero) finalStore := by
  simpa using firstEvaluation.wordMulMod secondEvaluation modulusEvaluation

theorem wordMulMod_nonzero
    {environment : Environment}
    {initialStore afterFirstStore afterSecondStore finalStore : Store}
    {first second modulus : Expr}
    {firstResult secondResult modulusResult : Word}
    (nonzero : modulusResult.val ≠ 0)
    (firstEvaluation :
      Evaluates environment initialStore first (.word firstResult) afterFirstStore)
    (secondEvaluation :
      Evaluates environment afterFirstStore second (.word secondResult)
        afterSecondStore)
    (modulusEvaluation :
      Evaluates environment afterSecondStore modulus (.word modulusResult)
        finalStore) :
    Evaluates environment initialStore
      (.ternary .wordMulMod first second modulus)
      (.word (Word.ofNatModulo
        ((firstResult.val * secondResult.val) % modulusResult.val))) finalStore := by
  simpa only [Word.mulMod_nonzero firstResult secondResult modulusResult nonzero] using
    firstEvaluation.wordMulMod secondEvaluation modulusEvaluation

end Evaluates

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.UnsignedDivision
/-! Focused value and evaluation interface for unsigned division and modulo. -/

set_option autoImplicit false

namespace Solcore.Core

namespace Word

@[simp] theorem udiv_zero (left : Word) :
    left.udiv Word.zero = Word.zero := by
  rfl

@[simp] theorem umod_zero (left : Word) :
    left.umod Word.zero = Word.zero := by
  rfl

theorem udiv_nonzero (left right : Word) (nonzero : right ≠ Word.zero) :
    left.udiv right = left / right := by
  have valueNonzero : right.val ≠ 0 := by
    intro valueZero
    apply nonzero
    exact Fin.ext (by
      change right.val = 0
      exact valueZero)
  simp [udiv, valueNonzero]

theorem umod_nonzero (left right : Word) (nonzero : right ≠ Word.zero) :
    left.umod right = left % right := by
  have valueNonzero : right.val ≠ 0 := by
    intro valueZero
    apply nonzero
    exact Fin.ext (by
      change right.val = 0
      exact valueZero)
  simp [umod, valueNonzero]

end Word

namespace BinaryOp

@[simp] theorem apply_wordDiv (left right : Word) :
    BinaryOp.wordDiv.apply (.word left) (.word right) =
      some (.word (left.udiv right)) := by
  rfl

@[simp] theorem apply_wordMod (left right : Word) :
    BinaryOp.wordMod.apply (.word left) (.word right) =
      some (.word (left.umod right)) := by
  rfl

end BinaryOp

namespace Evaluates

theorem wordDiv
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordDiv left right)
      (.word (leftValue.udiv rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordDiv_zero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.binary .wordDiv left right)
      (.word Word.zero) finalStore := by
  simpa using leftEvaluation.wordDiv rightEvaluation

theorem wordDiv_nonzero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (divisorNonzero : rightValue ≠ Word.zero)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordDiv left right)
      (.word (leftValue / rightValue)) finalStore := by
  simpa [Word.udiv_nonzero leftValue rightValue divisorNonzero] using
    leftEvaluation.wordDiv rightEvaluation

theorem wordMod
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordMod left right)
      (.word (leftValue.umod rightValue)) finalStore :=
  .binary leftEvaluation rightEvaluation rfl

theorem wordMod_zero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue : Word}
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.binary .wordMod left right)
      (.word Word.zero) finalStore := by
  simpa using leftEvaluation.wordMod rightEvaluation

theorem wordMod_nonzero
    {environment : Environment} {initialStore intermediateStore finalStore : Store}
    {left right : Expr} {leftValue rightValue : Word}
    (divisorNonzero : rightValue ≠ Word.zero)
    (leftEvaluation :
      Evaluates environment initialStore left (.word leftValue) intermediateStore)
    (rightEvaluation :
      Evaluates environment intermediateStore right (.word rightValue) finalStore) :
    Evaluates environment initialStore (.binary .wordMod left right)
      (.word (leftValue % rightValue)) finalStore := by
  simpa [Word.umod_nonzero leftValue rightValue divisorNonzero] using
    leftEvaluation.wordMod rightEvaluation

end Evaluates

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.UnaryPrimitives
/-! Focused proof interface for the two direct unary primitives. -/

set_option autoImplicit false

namespace Solcore.Core

namespace Word

@[simp] theorem bitNot_zero : Word.zero.bitNot = Word.maximum := by
  rfl

@[simp] theorem bitNot_maximum : Word.maximum.bitNot = Word.zero := by
  rfl

@[simp] theorem bitNot_involutive (value : Word) :
    value.bitNot.bitNot = value := by
  apply Fin.ext
  unfold bitNot
  have valueLe : value ≤ maximum := Fin.le_last value
  have innerLe : maximum - value ≤ maximum := Fin.le_last (maximum - value)
  rw [Fin.sub_val_of_le innerLe]
  rw [Fin.sub_val_of_le valueLe]
  simp only [maximum]
  omega

end Word

namespace HasType

theorem boolNot
    {context : Context} {definitions : DataEnvironment} {operand : Expr}
    (typing : HasType context operand .bool definitions) :
    HasType context (.unary .boolNot operand) .bool definitions :=
  .unary typing

theorem wordNot
    {context : Context} {definitions : DataEnvironment} {operand : Expr}
    (typing : HasType context operand .word definitions) :
    HasType context (.unary .wordNot operand) .word definitions :=
  .unary typing

end HasType

theorem infer_boolNot
    {context : Context} {definitions : DataEnvironment} {operand : Expr}
    (inferred : infer? context operand definitions = some .bool) :
    infer? context (.unary .boolNot operand) definitions = some .bool :=
  infer_complete ((infer_sound inferred).boolNot)

theorem infer_wordNot
    {context : Context} {definitions : DataEnvironment} {operand : Expr}
    (inferred : infer? context operand definitions = some .word) :
    infer? context (.unary .wordNot operand) definitions = some .word :=
  infer_complete ((infer_sound inferred).wordNot)

namespace Evaluates

theorem boolNot
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Bool}
    (evaluation :
      Evaluates environment initialStore operand (.bool value) finalStore) :
    Evaluates environment initialStore (.unary .boolNot operand)
      (.bool (!value)) finalStore :=
  .unary evaluation rfl

theorem boolNot_true
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.bool true) finalStore) :
    Evaluates environment initialStore (.unary .boolNot operand)
      (.bool false) finalStore := by
  simpa using evaluation.boolNot

theorem boolNot_false
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.bool false) finalStore) :
    Evaluates environment initialStore (.unary .boolNot operand)
      (.bool true) finalStore := by
  simpa using evaluation.boolNot

theorem wordNot
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr} {value : Word}
    (evaluation :
      Evaluates environment initialStore operand (.word value) finalStore) :
    Evaluates environment initialStore (.unary .wordNot operand)
      (.word value.bitNot) finalStore :=
  .unary evaluation rfl

theorem wordNot_zero
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.zero) finalStore) :
    Evaluates environment initialStore (.unary .wordNot operand)
      (.word Word.maximum) finalStore := by
  simpa using evaluation.wordNot

theorem wordNot_maximum
    {environment : Environment} {initialStore finalStore : Store}
    {operand : Expr}
    (evaluation :
      Evaluates environment initialStore operand (.word Word.maximum) finalStore) :
    Evaluates environment initialStore (.unary .wordNot operand)
      (.word Word.zero) finalStore := by
  simpa using evaluation.wordNot

end Evaluates

@[simp] theorem Expr.rename_boolNot
    (operand : Expr) (mapping : Renaming) :
    (Expr.unary .boolNot operand).rename mapping =
      .unary .boolNot (operand.rename mapping) := by
  rfl

@[simp] theorem Expr.rename_wordNot
    (operand : Expr) (mapping : Renaming) :
    (Expr.unary .wordNot operand).rename mapping =
      .unary .wordNot (operand.rename mapping) := by
  rfl

@[simp] theorem Expr.weakenAt_boolNot
    (operand : Expr) (cutoff : Nat) :
    (Expr.unary .boolNot operand).weakenAt cutoff =
      .unary .boolNot (operand.weakenAt cutoff) := by
  simp [Expr.weakenAt]

@[simp] theorem Expr.weakenAt_wordNot
    (operand : Expr) (cutoff : Nat) :
    (Expr.unary .wordNot operand).weakenAt cutoff =
      .unary .wordNot (operand.weakenAt cutoff) := by
  simp [Expr.weakenAt]

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.ShortCircuit
set_option autoImplicit false

namespace Solcore.Core

@[simp] theorem Expr.boolAnd_expansion (left right : Expr) :
    left.boolAnd right = .ifE left right (.bool false) :=
  rfl

@[simp] theorem Expr.boolOr_expansion (left right : Expr) :
    left.boolOr right = .ifE left (.bool true) right :=
  rfl

namespace HasType

theorem boolAnd
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .bool definitions)
    (rightTyping : HasType context right .bool definitions) :
    HasType context (left.boolAnd right) .bool definitions :=
  .ifE leftTyping rightTyping .bool

theorem boolOr
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftTyping : HasType context left .bool definitions)
    (rightTyping : HasType context right .bool definitions) :
    HasType context (left.boolOr right) .bool definitions :=
  .ifE leftTyping .bool rightTyping

end HasType

theorem infer_boolAnd
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .bool)
    (rightInferred : infer? context right definitions = some .bool) :
    infer? context (left.boolAnd right) definitions = some .bool :=
  infer_complete ((infer_sound leftInferred).boolAnd (infer_sound rightInferred))

theorem infer_boolOr
    {context : Context} {definitions : DataEnvironment} {left right : Expr}
    (leftInferred : infer? context left definitions = some .bool)
    (rightInferred : infer? context right definitions = some .bool) :
    infer? context (left.boolOr right) definitions = some .bool :=
  infer_complete ((infer_sound leftInferred).boolOr (infer_sound rightInferred))

namespace Evaluates

theorem boolAnd_false
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr}
    (leftEvaluation :
      Evaluates environment initialStore left (.bool false) finalStore) :
    Evaluates environment initialStore (left.boolAnd right)
      (.bool false) finalStore :=
  .ifFalse leftEvaluation .bool

theorem boolAnd_true
    {environment : Environment} {initialStore branchStore finalStore : Store}
    {left right : Expr} {result : Bool}
    (leftEvaluation :
      Evaluates environment initialStore left (.bool true) branchStore)
    (rightEvaluation :
      Evaluates environment branchStore right (.bool result) finalStore) :
    Evaluates environment initialStore (left.boolAnd right)
      (.bool result) finalStore :=
  .ifTrue leftEvaluation rightEvaluation

theorem boolOr_true
    {environment : Environment} {initialStore finalStore : Store}
    {left right : Expr}
    (leftEvaluation :
      Evaluates environment initialStore left (.bool true) finalStore) :
    Evaluates environment initialStore (left.boolOr right)
      (.bool true) finalStore :=
  .ifTrue leftEvaluation .bool

theorem boolOr_false
    {environment : Environment} {initialStore branchStore finalStore : Store}
    {left right : Expr} {result : Bool}
    (leftEvaluation :
      Evaluates environment initialStore left (.bool false) branchStore)
    (rightEvaluation :
      Evaluates environment branchStore right (.bool result) finalStore) :
    Evaluates environment initialStore (left.boolOr right)
      (.bool result) finalStore :=
  .ifFalse leftEvaluation rightEvaluation

end Evaluates

@[simp] theorem Expr.rename_boolAnd
    (left right : Expr) (mapping : Renaming) :
    (left.boolAnd right).rename mapping =
      (left.rename mapping).boolAnd (right.rename mapping) := by
  simp [Expr.boolAnd, Expr.rename]

@[simp] theorem Expr.rename_boolOr
    (left right : Expr) (mapping : Renaming) :
    (left.boolOr right).rename mapping =
      (left.rename mapping).boolOr (right.rename mapping) := by
  simp [Expr.boolOr, Expr.rename]

@[simp] theorem Expr.weakenAt_boolAnd
    (left right : Expr) (cutoff : Nat) :
    (left.boolAnd right).weakenAt cutoff =
      (left.weakenAt cutoff).boolAnd (right.weakenAt cutoff) := by
  simp [Expr.boolAnd, Expr.weakenAt]

@[simp] theorem Expr.weakenAt_boolOr
    (left right : Expr) (cutoff : Nat) :
    (left.boolOr right).weakenAt cutoff =
      (left.weakenAt cutoff).boolOr (right.weakenAt cutoff) := by
  simp [Expr.boolOr, Expr.weakenAt]

end Solcore.Core
end
