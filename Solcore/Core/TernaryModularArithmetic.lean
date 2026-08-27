import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value, application, and evaluation interface for ternary modular arithmetic. -/

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
