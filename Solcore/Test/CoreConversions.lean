import Solcore.Core.Check
import Solcore.Core.Machine

/-! Executable regressions for the derived boolean/word conversions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def testConversionValuesAndTypes : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let falseProgram : Program := {
    resultType := .word
    body := Expr.boolToWord (.bool false)
  }
  let trueProgram : Program := {
    resultType := .word
    body := Expr.boolToWord (.bool true)
  }
  let zeroProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word Word.zero)
  }
  let oneProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word one)
  }
  let twoProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word two)
  }
  let maximumProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word Word.maximum)
  }

  for program in [
      falseProgram, trueProgram, zeroProgram, oneProgram, twoProgram,
      maximumProgram
    ] do
    assertTrue program.check
      s!"derived conversion failed to type-check: {reprStr program.body}"

  assertTrue (falseProgram.run 4 == .done (.word Word.zero))
    "boolToWord must convert false to zero"
  assertTrue (trueProgram.run 4 == .done (.word one))
    "boolToWord must convert true to one"
  assertTrue (zeroProgram.run 7 == .done (.bool false))
    "wordToBool must convert zero to false"
  assertTrue (oneProgram.run 7 == .done (.bool true))
    "wordToBool must convert one to true"
  assertTrue (twoProgram.run 7 == .done (.bool true))
    "wordToBool truthiness must remain distinct from strict ABI boolean decoding"
  assertTrue (maximumProgram.run 7 == .done (.bool true))
    "wordToBool must convert every nonzero word, including the maximum, to true"

  let wrongBoolInput : Program := {
    resultType := .word
    body := Expr.boolToWord .unit
  }
  let wrongWordInput : Program := {
    resultType := .bool
    body := Expr.wordToBool .unit
  }
  assertTrue (!wrongBoolInput.check)
    "boolToWord must reject a non-boolean operand"
  assertTrue (!wrongWordInput.check)
    "wordToBool must reject a non-word operand"
  assertTrue (wrongBoolInput.run 2 == .fault (.expectedBool .unit))
    "the unchecked boolToWord expansion must expose its boolean-shape fault"
  assertTrue
    (wrongWordInput.run 5 ==
      .fault (.invalidBinaryOperands .wordEq .unit (.word Word.zero)))
    "the unchecked wordToBool expansion must expose its word-comparison fault"

private def testExactFuelAndSingleEvaluation : IO Unit := do
  let one := Word.ofNatModulo 1
  let boolProgram : Program := {
    resultType := .word
    body := Expr.boolToWord (.bool true)
  }
  assertTrue (boolProgram.run 3 == .outOfFuel)
    "three transitions must be insufficient for boolToWord"
  assertTrue (boolProgram.run 4 == .done (.word one))
    "boolToWord must finish at its four-transition boundary"

  let wordProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word Word.maximum)
  }
  assertTrue (wordProgram.run 6 == .outOfFuel)
    "six transitions must be insufficient for wordToBool"
  assertTrue (wordProgram.run 7 == .done (.bool true))
    "wordToBool must finish at its seven-transition boundary"

  let effectfulBool : Program := {
    resultType := .word
    body :=
      Expr.boolToWord
        (.letE (.newCell .unit .unit) (.bool true))
  }
  assertTrue effectfulBool.check
    "boolToWord must accept an effectful boolean operand"
  assertTrue
    (effectfulBool.runStateful 9 == .done (.word one) [.unit])
    "boolToWord must evaluate its operand exactly once before selecting the result"

  let effectfulWord : Program := {
    resultType := .bool
    body :=
      Expr.wordToBool
        (.letE (.newCell .unit .unit) (.word Word.maximum))
  }
  assertTrue effectfulWord.check
    "wordToBool must accept an effectful word operand"
  assertTrue
    (effectfulWord.runStateful 12 == .done (.bool true) [.unit])
    "wordToBool must evaluate its operand exactly once before comparison"

private def testWordIsZero : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let zeroProgram : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word Word.zero)
  }
  let oneProgram : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word one)
  }
  let twoProgram : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word two)
  }
  let maximumProgram : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word Word.maximum)
  }

  for program in [zeroProgram, oneProgram, twoProgram, maximumProgram] do
    assertTrue program.check
      s!"wordIsZero failed to type-check as word: {reprStr program.body}"

  assertTrue (zeroProgram.run 8 == .done (.word one))
    "wordIsZero must map zero to word one"
  assertTrue (oneProgram.run 8 == .done (.word Word.zero))
    "wordIsZero must map word one to word zero"
  assertTrue (twoProgram.run 8 == .done (.word Word.zero))
    "wordIsZero must map word two to word zero"
  assertTrue (maximumProgram.run 8 == .done (.word Word.zero))
    "wordIsZero must map the maximum word to word zero"

  let wrongInput : Program := {
    resultType := .word
    body := Expr.wordIsZero .unit
  }
  assertTrue (!wrongInput.check)
    "wordIsZero must reject a non-word operand"
  assertTrue
    (wrongInput.run 5 ==
      .fault (.invalidBinaryOperands .wordEq .unit (.word Word.zero)))
    "the unchecked wordIsZero expansion must expose its word-comparison fault"

  assertTrue (zeroProgram.run 7 == .outOfFuel)
    "seven transitions must be insufficient for wordIsZero"
  assertTrue (zeroProgram.run 8 == .done (.word one))
    "wordIsZero must finish at its eight-transition boundary"

  let effectfulProgram : Program := {
    resultType := .word
    body :=
      Expr.wordIsZero
        (.letE (.newCell .unit .unit) (.word Word.zero))
  }
  assertTrue effectfulProgram.check
    "wordIsZero must accept an effectful word operand"
  assertTrue
    (effectfulProgram.runStateful 13 == .done (.word one) [.unit])
    "wordIsZero must evaluate its operand exactly once before comparing with zero"

  let booleanTruthiness : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word Word.zero)
  }
  assertTrue booleanTruthiness.check
    "wordToBool must retain its boolean result type"
  assertTrue (booleanTruthiness.run 7 == .done (.bool false))
    "wordToBool zero must remain boolean false, distinct from wordIsZero's word one"
  let wrongDeclaredType : Program := {
    resultType := .bool
    body := Expr.wordIsZero (.word Word.zero)
  }
  assertTrue (!wrongDeclaredType.check)
    "wordIsZero must not be confused with the boolean-valued wordToBool helper"

private def testWordIsNonzero : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let zeroProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero (.word Word.zero)
  }
  let oneProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero (.word one)
  }
  let twoProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero (.word two)
  }
  let maximumProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero (.word Word.maximum)
  }

  for program in [zeroProgram, oneProgram, twoProgram, maximumProgram] do
    assertTrue program.check
      s!"wordIsNonzero failed to type-check as word: {reprStr program.body}"

  assertTrue (zeroProgram.run 10 == .done (.word Word.zero))
    "wordIsNonzero must map zero to word zero"
  assertTrue (oneProgram.run 10 == .done (.word one))
    "wordIsNonzero must map word one to word one"
  assertTrue (twoProgram.run 10 == .done (.word one))
    "wordIsNonzero must map word two to word one"
  assertTrue (maximumProgram.run 10 == .done (.word one))
    "wordIsNonzero must map the maximum word to word one"

  let wrongInput : Program := {
    resultType := .word
    body := Expr.wordIsNonzero .unit
  }
  let wrongDeclaredType : Program := {
    resultType := .bool
    body := Expr.wordIsNonzero (.word one)
  }
  assertTrue (!wrongInput.check)
    "wordIsNonzero must reject a non-word operand"
  assertTrue (!wrongDeclaredType.check)
    "wordIsNonzero must retain its word result type"
  assertTrue
    (wrongInput.run 6 ==
      .fault (.invalidBinaryOperands .wordEq .unit (.word Word.zero)))
    "the unchecked expansion must expose its inner word comparison fault"

  assertTrue (zeroProgram.run 9 == .outOfFuel)
    "nine transitions must be insufficient for canonical wordIsNonzero"
  assertTrue (zeroProgram.run 10 == .done (.word Word.zero))
    "canonical wordIsNonzero must finish at its ten-transition boundary"

  let effectfulOperand : Expr :=
    .letE
      (.newCell .word (.word Word.zero))
      (.letE
        (.storeCell (.var 0) (.word Word.maximum))
        (.word one))
  let effectfulProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero effectfulOperand
  }
  assertTrue effectfulProgram.check
    "wordIsNonzero must accept an allocating and writing word operand"
  assertTrue
    (effectfulProgram.runStateful 22 ==
      .done (.word one) [.word Word.maximum])
    "wordIsNonzero must evaluate its operand once and preserve its updated store"

  let booleanTruthiness : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word one)
  }
  let zeroPredicate : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word one)
  }
  assertTrue (booleanTruthiness.run 7 == .done (.bool true))
    "wordToBool must remain boolean-valued"
  assertTrue (zeroPredicate.run 8 == .done (.word Word.zero))
    "wordIsZero must remain the inverse word-valued predicate"
  assertTrue (oneProgram.run 10 == .done (.word one))
    "wordIsNonzero must remain distinct from wordToBool and wordIsZero"

/-- Cover truth conversion and the word-valued zero/nonzero predicates, including
typing, raw faults, evaluation order, and exact fuel. -/
def testCoreConversions : IO Unit := do
  testConversionValuesAndTypes
  testExactFuelAndSingleEvaluation
  testWordIsZero
  testWordIsNonzero

end Tests
