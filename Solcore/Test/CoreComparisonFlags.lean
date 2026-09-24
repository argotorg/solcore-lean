import Solcore.Core.Check
import Solcore.Core.Derived
import Solcore.Core.Machine

/-! Executable regressions for derived word-valued comparison flags. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def allocatingWritingWord
    (initial written result : Word) : Expr :=
  .letE
    (.newCell .word (.word initial))
    (.letE
      (.storeCell (.var 0) (.word written))
      (.word result))

private def testValuesAndTypes : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let equalMaximum : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.word Word.maximum) (.word Word.maximum)
  }
  let unequalBoundary : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.word Word.zero) (.word Word.maximum)
  }
  let maximumGreater : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word Word.maximum) (.word Word.zero)
  }
  let zeroNotGreater : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word Word.zero) (.word Word.maximum)
  }
  let equalNotGreater : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word Word.maximum) (.word Word.maximum)
  }
  let ordinaryGreater : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word two) (.word one)
  }

  for program in [
      equalMaximum, unequalBoundary, maximumGreater, zeroNotGreater,
      equalNotGreater, ordinaryGreater
    ] do
    assertTrue program.check
      s!"comparison flag failed to type-check as word: {reprStr program.body}"

  assertTrue (equalMaximum.run 8 == .done (.word one))
    "wordEqFlag must map equal maximum words to one"
  assertTrue (unequalBoundary.run 8 == .done (.word Word.zero))
    "wordEqFlag must map unequal boundary words to zero"
  assertTrue (maximumGreater.run 8 == .done (.word one))
    "wordGtFlag must compare the maximum word above zero"
  assertTrue (zeroNotGreater.run 8 == .done (.word Word.zero))
    "wordGtFlag must not compare zero above the maximum word"
  assertTrue (equalNotGreater.run 8 == .done (.word Word.zero))
    "wordGtFlag must remain strict at the maximum-word boundary"
  assertTrue (ordinaryGreater.run 8 == .done (.word one))
    "wordGtFlag must use unsigned greater-than"

  let eqBadLeft : Program := {
    resultType := .word
    body := Expr.wordEqFlag .unit (.word Word.zero)
  }
  let eqBadRight : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.word Word.zero) .unit
  }
  let gtBadLeft : Program := {
    resultType := .word
    body := Expr.wordGtFlag .unit (.word Word.zero)
  }
  let gtBadRight : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word Word.zero) .unit
  }
  for program in [eqBadLeft, eqBadRight, gtBadLeft, gtBadRight] do
    assertTrue (!program.check)
      s!"comparison flag accepted a non-word operand: {reprStr program.body}"
  assertTrue
    (eqBadLeft.run 5 ==
      .fault (.invalidBinaryOperands .wordEq .unit (.word Word.zero)))
    "unchecked wordEqFlag must expose its invalid left operand"
  assertTrue
    (gtBadRight.run 5 ==
      .fault (.invalidBinaryOperands .wordGt (.word Word.zero) .unit))
    "unchecked wordGtFlag must expose its invalid right operand"

  let wrongEqResult : Program := {
    resultType := .bool
    body := Expr.wordEqFlag (.word Word.zero) (.word Word.zero)
  }
  let wrongGtResult : Program := {
    resultType := .bool
    body := Expr.wordGtFlag (.word one) (.word Word.zero)
  }
  assertTrue (!wrongEqResult.check)
    "wordEqFlag must retain its word result type"
  assertTrue (!wrongGtResult.check)
    "wordGtFlag must retain its word result type"

private def testRawFaultOrder : IO Unit := do
  let one := Word.ofNatModulo 1
  let rightWithEffect :=
    allocatingWritingWord Word.zero one Word.zero
  let leftFault : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.var 99) rightWithEffect
  }
  match leftFault.runStateful 2 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "a left fault must prevent evaluation of the right operand"
  | result =>
      throw (IO.userError
        s!"wordEqFlag exposed the wrong left-first fault: {reprStr result}")

  let leftWithEffect :=
    allocatingWritingWord Word.zero one Word.maximum
  let rightFault : Program := {
    resultType := .word
    body := Expr.wordGtFlag leftWithEffect (.var 100)
  }
  match rightFault.runStateful 16 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "the right fault must observe the left operand's completed store"
  | result =>
      throw (IO.userError
        s!"wordGtFlag exposed the wrong right-second fault: {reprStr result}")

private def testEffectsAndExactFuel : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let literalEq : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.word Word.zero) (.word Word.zero)
  }
  let literalGt : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word one) (.word Word.zero)
  }
  assertTrue (literalEq.run 7 == .outOfFuel)
    "seven transitions must be insufficient for wordEqFlag"
  assertTrue (literalEq.run 8 == .done (.word one))
    "wordEqFlag must finish at its eight-transition boundary"
  assertTrue (literalGt.run 7 == .outOfFuel)
    "seven transitions must be insufficient for wordGtFlag"
  assertTrue (literalGt.run 8 == .done (.word one))
    "wordGtFlag must finish at its eight-transition boundary"

  let left := allocatingWritingWord Word.zero one Word.maximum
  let right := allocatingWritingWord Word.zero two Word.zero
  let effectfulEq : Program := {
    resultType := .word
    body := Expr.wordEqFlag left right
  }
  let effectfulGt : Program := {
    resultType := .word
    body := Expr.wordGtFlag left right
  }
  for program in [effectfulEq, effectfulGt] do
    assertTrue program.check
      s!"effectful comparison flag failed to type-check: {reprStr program.body}"
    assertTrue (program.run 31 == .outOfFuel)
      "thirty-one transitions must be insufficient for effectful flags"

  assertTrue
    (effectfulEq.runStateful 32 ==
      .done (.word Word.zero) [.word one, .word two])
    "wordEqFlag must evaluate left then right exactly once and preserve the store"
  assertTrue
    (effectfulGt.runStateful 32 ==
      .done (.word one) [.word one, .word two])
    "wordGtFlag must evaluate left then right exactly once and preserve the store"

private def testBooleanCompatibility : IO Unit := do
  let boolEq : Program := {
    resultType := .bool
    body := .binary .wordEq (.word Word.maximum) (.word Word.maximum)
  }
  let boolGt : Program := {
    resultType := .bool
    body := .binary .wordGt (.word Word.maximum) (.word Word.zero)
  }
  assertTrue boolEq.check
    "the existing wordEq operation must remain boolean-valued"
  assertTrue boolGt.check
    "the existing wordGt operation must remain boolean-valued"
  assertTrue (boolEq.run 5 == .done (.bool true))
    "wordEq must retain its boolean result"
  assertTrue (boolGt.run 5 == .done (.bool true))
    "wordGt must retain its boolean result"

/-- Cover values, types, fault order, effects, fuel, and compatibility with the
boolean-valued comparison primitives. -/
def testCoreComparisonFlags : IO Unit := do
  testValuesAndTypes
  testRawFaultOrder
  testEffectsAndExactFuel
  testBooleanCompatibility

end Tests
