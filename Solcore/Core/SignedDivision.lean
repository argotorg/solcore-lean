import Solcore.Core.Eval

set_option autoImplicit false

namespace Solcore.Core

/-! Focused value, application, and evaluation interface for signed division and modulo. -/

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
