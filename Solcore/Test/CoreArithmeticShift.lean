import Solcore.Core.ArithmeticShift
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for internal arithmetic right shift. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word (value : Nat) : Word := Word.ofNatModulo value
private def zero : Word := Word.zero
private def one : Word := word 1
private def two : Word := word 2
private def shift255 : Word := word 255
private def shift256 : Word := word 256
private def highBit : Word := word (2 ^ 255)
private def highBitShiftOne : Word := word (wordModulus - 2 ^ 254)
private def negativeTwo : Word := word (wordModulus - 2)
private def negativeThree : Word := word (wordModulus - 3)

example : highBit.shiftArithmeticRight zero = highBit :=
  Word.shiftArithmeticRight_zero highBit
example : (word 4).shiftArithmeticRight one = word (4 / 2 ^ one.val) :=
  Word.shiftArithmeticRight_of_lt_256_nonnegative (word 4) one
    (by decide) (by decide)
example : negativeThree.shiftArithmeticRight one =
    word (wordModulus - 1 -
      ((wordModulus - 1 - negativeThree.val) / 2 ^ one.val)) :=
  Word.shiftArithmeticRight_of_lt_256_negative negativeThree one
    (by decide) (by decide)
example : one.shiftArithmeticRight shift256 = zero :=
  Word.shiftArithmeticRight_of_ge_256_nonnegative one shift256
    (by decide) (by decide)
example : highBit.shiftArithmeticRight shift256 = Word.maximum :=
  Word.shiftArithmeticRight_of_ge_256_negative highBit shift256
    (by decide) (by decide)

example : BinaryOp.wordSar.apply (.word highBit) (.word one) =
    some (.word (highBit.shiftArithmeticRight one)) :=
  BinaryOp.apply_wordSar highBit one
example : Evaluates [] [] (.binary .wordSar (.word highBit) (.word one))
    (.word (highBit.shiftArithmeticRight one)) [] :=
  Evaluates.wordSar .word .word
example : Evaluates [] [] (.binary .wordSar (.word (word 4)) (.word one))
    (.word two) [] :=
  Evaluates.wordSar_lt_256_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSar (.word negativeTwo) (.word one))
    (.word Word.maximum) [] :=
  Evaluates.wordSar_lt_256_negative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSar (.word one) (.word shift256))
    (.word zero) [] :=
  Evaluates.wordSar_ge_256_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSar (.word highBit) (.word shift256))
    (.word Word.maximum) [] :=
  Evaluates.wordSar_ge_256_negative (by decide) (by decide) .word .word

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
  let cases : List (String × Word × Word × Word) := [
    ("positive four by one", word 4, one, two),
    ("high bit by zero", highBit, zero, highBit),
    ("high bit by one", highBit, one, highBitShiftOne),
    ("high bit by 255", highBit, shift255, Word.maximum),
    ("high bit by 256", highBit, shift256, Word.maximum),
    ("maximum by one", Word.maximum, one, Word.maximum),
    ("maximum by maximum shift", Word.maximum, Word.maximum, Word.maximum),
    ("negative two by one", negativeTwo, one, Word.maximum),
    ("negative three by one", negativeThree, one, negativeTwo),
    ("positive one by 255", one, shift255, zero),
    ("positive one by 256", one, shift256, zero),
    ("positive one by maximum shift", one, Word.maximum, zero)
  ]
  for (name, value, shift, expected) in cases do
    let witness := wordProgram (.binary .wordSar (.word value) (.word shift))
    assertTrue witness.check s!"wordSar {name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordSar {name} finished below the literal fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"wordSar {name} failed at the literal fuel boundary"

  let validBody : Expr := .binary .wordSar (.word highBit) (.word one)
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordSar accepted a boolean result type"

  let wrongLeft : Expr := .binary .wordSar .unit (.word one)
  let wrongRight : Expr := .binary .wordSar (.word highBit) .unit
  assertTrue (!(wordProgram wrongLeft).check) "wordSar accepted a non-word value"
  assertTrue (!(wordProgram wrongRight).check) "wordSar accepted a non-word shift"
  assertTrue
    ((wordProgram wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands .wordSar .unit (.word one)))
    "raw wordSar did not expose its invalid left operand"
  assertTrue
    ((wordProgram wrongRight).run 5 ==
      .fault (.invalidBinaryOperands .wordSar (.word highBit) .unit))
    "raw wordSar did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let effectfulShift := allocatingWritingWord zero one one
  let valueFault : Expr := .binary .wordSar (.var 99) effectfulShift
  match (wordProgram valueFault).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordSar evaluated shift after a value fault"
  | result =>
      throw (IO.userError s!"wordSar exposed the wrong value fault: {reprStr result}")

  let effectfulValue := allocatingWritingWord zero one highBit
  let shiftFault : Expr := .binary .wordSar effectfulValue (.var 100)
  match (wordProgram shiftFault).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordSar shift fault did not observe the value effect"
  | result =>
      throw (IO.userError s!"wordSar exposed the wrong shift fault: {reprStr result}")

private def testEffectfulOperands : IO Unit := do
  let value := allocatingWritingWord zero one highBit
  let shift := allocatingWritingWord zero two one
  let witness := wordProgram (.binary .wordSar value shift)
  assertTrue witness.check "effectful wordSar failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordSar finished below exact fuel"
  assertTrue
    (witness.runStateful 29 ==
      .done (.word highBitShiftOne) [.word one, .word two])
    "wordSar did not evaluate value then shift exactly once or retain the store"

/-- Cover all eleven theorems plus values, types, faults, effects, store, and fuel. -/
def testCoreArithmeticShift : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
