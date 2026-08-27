import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

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

private def testFrozenWireProjection : IO Unit := do
  let boolConversion := Expr.boolToWord (.bool true)
  let wordConversion := Expr.wordToBool (.word Word.maximum)

  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? boolConversion).isSome
    "boolToWord must remain a normal v1 if/word expression"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? boolConversion).isSome
    "boolToWord must project through the existing v2 expression forms"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? wordConversion).isSome
    "wordToBool must project through the existing v2 primitive expression forms"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? wordConversion).isNone
    "v1 must continue rejecting the M1c primitives used by wordToBool"

/-- Cover truth conversion, typing, raw faults, evaluation order, exact fuel,
and the unchanged frozen-wire boundary. -/
def testCoreConversions : IO Unit := do
  testConversionValuesAndTypes
  testExactFuelAndSingleEvaluation
  testFrozenWireProjection

end Tests
