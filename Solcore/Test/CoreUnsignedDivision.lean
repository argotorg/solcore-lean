import Solcore.Core.UnsignedDivision
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for unsigned division and modulo. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def zero : Word := Word.zero
private def one : Word := Word.ofNatModulo 1
private def two : Word := Word.ofNatModulo 2
private def three : Word := Word.ofNatModulo 3
private def seven : Word := Word.ofNatModulo 7

example : seven.udiv zero = zero := Word.udiv_zero seven
example : seven.umod zero = zero := Word.umod_zero seven
example : seven.udiv three = seven / three :=
  Word.udiv_nonzero seven three (by decide)
example : seven.umod three = seven % three :=
  Word.umod_nonzero seven three (by decide)

example : BinaryOp.wordDiv.apply (.word seven) (.word three) =
    some (.word (seven.udiv three)) :=
  BinaryOp.apply_wordDiv seven three
example : BinaryOp.wordMod.apply (.word seven) (.word three) =
    some (.word (seven.umod three)) :=
  BinaryOp.apply_wordMod seven three

example : Evaluates [] [] (.binary .wordDiv (.word seven) (.word three))
    (.word (seven.udiv three)) [] :=
  Evaluates.wordDiv .word .word
example : Evaluates [] [] (.binary .wordDiv (.word seven) (.word zero))
    (.word zero) [] :=
  Evaluates.wordDiv_zero .word .word
example : Evaluates [] [] (.binary .wordDiv (.word seven) (.word three))
    (.word (seven / three)) [] :=
  Evaluates.wordDiv_nonzero (by decide) .word .word

example : Evaluates [] [] (.binary .wordMod (.word seven) (.word three))
    (.word (seven.umod three)) [] :=
  Evaluates.wordMod .word .word
example : Evaluates [] [] (.binary .wordMod (.word seven) (.word zero))
    (.word zero) [] :=
  Evaluates.wordMod_zero .word .word
example : Evaluates [] [] (.binary .wordMod (.word seven) (.word three))
    (.word (seven % three)) [] :=
  Evaluates.wordMod_nonzero (by decide) .word .word

private def wordProgram (body : Expr) : Program := {
  resultType := .word
  body
}

private def allocatingWritingWord
    (initial written result : Word) : Expr :=
  .letE
    (.newCell .word (.word initial))
    (.letE
      (.storeCell (.var 0) (.word written))
      (.word result))

private def testValuesTypesAndLiteralFuel : IO Unit := do
  let maximum := Word.maximum
  let cases : List (String × Program × Value) := [
    ("seven div three", wordProgram
      (.binary .wordDiv (.word seven) (.word three)), .word two),
    ("seven mod three", wordProgram
      (.binary .wordMod (.word seven) (.word three)), .word one),
    ("three div seven", wordProgram
      (.binary .wordDiv (.word three) (.word seven)), .word zero),
    ("three mod seven", wordProgram
      (.binary .wordMod (.word three) (.word seven)), .word three),
    ("zero numerator div", wordProgram
      (.binary .wordDiv (.word zero) (.word three)), .word zero),
    ("zero numerator mod", wordProgram
      (.binary .wordMod (.word zero) (.word three)), .word zero),
    ("zero divisor div", wordProgram
      (.binary .wordDiv (.word seven) (.word zero)), .word zero),
    ("zero divisor mod", wordProgram
      (.binary .wordMod (.word seven) (.word zero)), .word zero),
    ("zero div zero", wordProgram
      (.binary .wordDiv (.word zero) (.word zero)), .word zero),
    ("zero mod zero", wordProgram
      (.binary .wordMod (.word zero) (.word zero)), .word zero),
    ("one div maximum", wordProgram
      (.binary .wordDiv (.word one) (.word maximum)), .word zero),
    ("one mod maximum", wordProgram
      (.binary .wordMod (.word one) (.word maximum)), .word one),
    ("maximum div one", wordProgram
      (.binary .wordDiv (.word maximum) (.word one)), .word maximum),
    ("maximum mod one", wordProgram
      (.binary .wordMod (.word maximum) (.word one)), .word zero),
    ("maximum div maximum", wordProgram
      (.binary .wordDiv (.word maximum) (.word maximum)), .word one),
    ("maximum mod maximum", wordProgram
      (.binary .wordMod (.word maximum) (.word maximum)), .word zero)
  ]
  for (name, witness, expected) in cases do
    assertTrue witness.check s!"{name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done expected)
      s!"{name} failed at the literal binary fuel boundary"

  for body in [
      Expr.binary .wordDiv .unit (.word one),
      Expr.binary .wordDiv (.word one) .unit,
      Expr.binary .wordMod .unit (.word one),
      Expr.binary .wordMod (.word one) .unit
    ] do
    assertTrue (!(wordProgram body).check)
      s!"unsigned division family accepted a non-word operand: {reprStr body}"

  for body in [
      Expr.binary .wordDiv (.word seven) (.word three),
      Expr.binary .wordMod (.word seven) (.word three)
    ] do
    let wrongResult : Program := { resultType := .bool, body }
    assertTrue (!wrongResult.check)
      s!"unsigned division family was accepted with bool result: {reprStr body}"

  assertTrue
    ((wordProgram (.binary .wordDiv .unit (.word one))).run 5 ==
      .fault (.invalidBinaryOperands .wordDiv .unit (.word one)))
    "raw wordDiv did not expose its invalid left operand"
  assertTrue
    ((wordProgram (.binary .wordDiv (.word one) .unit)).run 5 ==
      .fault (.invalidBinaryOperands .wordDiv (.word one) .unit))
    "raw wordDiv did not expose its invalid right operand"
  assertTrue
    ((wordProgram (.binary .wordMod .unit (.word one))).run 5 ==
      .fault (.invalidBinaryOperands .wordMod .unit (.word one)))
    "raw wordMod did not expose its invalid left operand"
  assertTrue
    ((wordProgram (.binary .wordMod (.word one) .unit)).run 5 ==
      .fault (.invalidBinaryOperands .wordMod (.word one) .unit))
    "raw wordMod did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let rightWithEffect := allocatingWritingWord zero one zero
  for (name, body) in [
      ("wordDiv", Expr.binary .wordDiv (.var 99) rightWithEffect),
      ("wordMod", Expr.binary .wordMod (.var 99) rightWithEffect)
    ] do
    match (wordProgram body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{name} evaluated its divisor after a numerator fault"
    | result =>
        throw (IO.userError s!"{name} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord zero one seven
  for (name, body) in [
      ("wordDiv", Expr.binary .wordDiv leftWithEffect (.var 100)),
      ("wordMod", Expr.binary .wordMod leftWithEffect (.var 100))
    ] do
    match (wordProgram body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one])
          s!"{name} divisor fault did not observe the completed numerator store"
    | result =>
        throw (IO.userError s!"{name} exposed the wrong right fault: {reprStr result}")

private def testEffectfulZeroDivisor : IO Unit := do
  let left := allocatingWritingWord zero one seven
  let right := allocatingWritingWord zero two zero
  for (name, body) in [
      ("wordDiv", Expr.binary .wordDiv left right),
      ("wordMod", Expr.binary .wordMod left right)
    ] do
    let witness := wordProgram body
    assertTrue witness.check s!"effectful zero-divisor {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful zero-divisor {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.word zero) [.word one, .word two])
      s!"{name} did not evaluate numerator then zero divisor exactly once"

/-- Cover all named theorems plus values, types, faults, effects, and fuel. -/
def testCoreUnsignedDivision : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulZeroDivisor

end Tests
