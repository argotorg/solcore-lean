import Solcore.Core.ByteSelection
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for internal word byte selection. -/

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
private def value1122 : Word := word 0x1122

example : (word 30).byteAt value1122 = word 0x11 :=
  Word.byteAt_index30_1122
example : (word 31).byteAt value1122 = word 0x22 :=
  Word.byteAt_index31_1122
example : (word 0).byteAt zero = zero := Word.byteAt_zero (word 0)
example : (word 31).byteAt value1122 =
    word ((value1122.val / 2 ^ (8 * (31 - (word 31).val))) % 256) :=
  Word.byteAt_of_lt_32 (word 31) value1122 (by decide)
example : (word 32).byteAt value1122 = zero :=
  Word.byteAt_of_ge_32 (word 32) value1122 (by decide)

example : BinaryOp.wordByte.apply (.word (word 30)) (.word value1122) =
    some (.word ((word 30).byteAt value1122)) :=
  BinaryOp.apply_wordByte (word 30) value1122
example : Evaluates [] []
    (.binary .wordByte (.word (word 30)) (.word value1122))
    (.word ((word 30).byteAt value1122)) [] :=
  Evaluates.wordByte .word .word
example : Evaluates [] []
    (.binary .wordByte (.word (word 30)) (.word value1122))
    (.word (word 0x11)) [] :=
  Evaluates.wordByte_lt_32 (by decide) .word .word
example : Evaluates [] []
    (.binary .wordByte (.word (word 32)) (.word value1122))
    (.word zero) [] :=
  Evaluates.wordByte_ge_32 (by decide) .word .word

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
    ("1122 index 0", word 0, value1122, zero),
    ("1122 index 29", word 29, value1122, zero),
    ("1122 index 30", word 30, value1122, word 0x11),
    ("1122 index 31", word 31, value1122, word 0x22),
    ("1122 index 32", word 32, value1122, zero),
    ("1122 maximum index", Word.maximum, value1122, zero),
    ("zero value index 0", word 0, zero, zero),
    ("zero value index 31", word 31, zero, zero),
    ("maximum value index 0", word 0, Word.maximum, word 0xff),
    ("maximum value index 31", word 31, Word.maximum, word 0xff)
  ]
  for (name, index, value, expected) in cases do
    let witness := wordProgram (.binary .wordByte (.word index) (.word value))
    assertTrue witness.check s!"wordByte {name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordByte {name} finished below the literal fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"wordByte {name} failed at the literal fuel boundary"

  let validBody : Expr := .binary .wordByte (.word (word 30)) (.word value1122)
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordByte accepted a boolean result type"

  let wrongLeft : Expr := .binary .wordByte .unit (.word value1122)
  let wrongRight : Expr := .binary .wordByte (.word (word 30)) .unit
  assertTrue (!(wordProgram wrongLeft).check) "wordByte accepted a non-word index"
  assertTrue (!(wordProgram wrongRight).check) "wordByte accepted a non-word value"
  assertTrue
    ((wordProgram wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands .wordByte .unit (.word value1122)))
    "raw wordByte did not expose its invalid left operand"
  assertTrue
    ((wordProgram wrongRight).run 5 ==
      .fault (.invalidBinaryOperands .wordByte (.word (word 30)) .unit))
    "raw wordByte did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let effectfulValue := allocatingWritingWord zero one value1122
  let leftFault : Expr := .binary .wordByte (.var 99) effectfulValue
  match (wordProgram leftFault).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordByte evaluated its value operand after an index fault"
  | result =>
      throw (IO.userError s!"wordByte exposed the wrong index fault: {reprStr result}")

  let effectfulIndex := allocatingWritingWord zero one (word 30)
  let rightFault : Expr := .binary .wordByte effectfulIndex (.var 100)
  match (wordProgram rightFault).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordByte value fault did not observe the index effect"
  | result =>
      throw (IO.userError s!"wordByte exposed the wrong value fault: {reprStr result}")

private def testEffectfulOperands : IO Unit := do
  let index := allocatingWritingWord zero one (word 30)
  let value := allocatingWritingWord zero two value1122
  let witness := wordProgram (.binary .wordByte index value)
  assertTrue witness.check "effectful wordByte failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordByte finished below exact fuel"
  assertTrue
    (witness.runStateful 29 == .done (.word (word 0x11)) [.word one, .word two])
    "wordByte did not evaluate index then value exactly once or retain the store"

/-- Cover all nine theorems plus values, types, faults, effects, store, and fuel. -/
def testCoreByteSelection : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
