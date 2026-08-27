import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused correctness and evaluation interface for modular word powers. -/

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
