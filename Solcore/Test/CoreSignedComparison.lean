import Solcore.Core.SignedComparison
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for internal signed word comparison. -/

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
private def highBit : Word := word (2 ^ 255)
private def positiveMaximum : Word := word (2 ^ 255 - 1)

example : zero.signedGt zero = false := Word.signedGt_self zero
example : one.signedGt zero = decide (one > zero) :=
  Word.signedGt_both_nonnegative one zero (by decide) (by decide)
example : Word.maximum.signedGt highBit =
    decide (Word.maximum > highBit) :=
  Word.signedGt_both_negative Word.maximum highBit (by decide) (by decide)
example : zero.signedGt Word.maximum = true :=
  Word.signedGt_nonnegative_negative zero Word.maximum (by decide) (by decide)
example : Word.maximum.signedGt zero = false :=
  Word.signedGt_negative_nonnegative Word.maximum zero (by decide) (by decide)

example : BinaryOp.wordSgt.apply (.word one) (.word zero) =
    some (.bool (one.signedGt zero)) :=
  BinaryOp.apply_wordSgt one zero
example : Evaluates [] [] (.binary .wordSgt (.word one) (.word zero))
    (.bool (one.signedGt zero)) [] :=
  Evaluates.wordSgt .word .word
example : Evaluates [] [] (.binary .wordSgt (.word one) (.word zero))
    (.bool true) [] :=
  Evaluates.wordSgt_both_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] []
    (.binary .wordSgt (.word Word.maximum) (.word highBit))
    (.bool true) [] :=
  Evaluates.wordSgt_both_negative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSgt (.word zero) (.word Word.maximum))
    (.bool true) [] :=
  Evaluates.wordSgt_nonnegative_negative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSgt (.word highBit) (.word zero))
    (.bool false) [] :=
  Evaluates.wordSgt_negative_nonnegative (by decide) (by decide) .word .word

private def boolProgram (body : Expr) : Program := {
  resultType := .bool
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
  let cases : List (String × Word × Word × Bool) := [
    ("zero above zero", zero, zero, false),
    ("one above zero", one, zero, true),
    ("zero above one", zero, one, false),
    ("positive maximum above zero", positiveMaximum, zero, true),
    ("zero above positive maximum", zero, positiveMaximum, false),
    ("high bit above zero", highBit, zero, false),
    ("zero above maximum", zero, Word.maximum, true),
    ("maximum above zero", Word.maximum, zero, false),
    ("maximum above high bit", Word.maximum, highBit, true),
    ("high bit above maximum", highBit, Word.maximum, false),
    ("maximum above maximum", Word.maximum, Word.maximum, false)
  ]
  for (name, left, right, expected) in cases do
    let witness := boolProgram (.binary .wordSgt (.word left) (.word right))
    assertTrue witness.check s!"wordSgt {name} failed to type-check as bool"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordSgt {name} finished below the literal fuel boundary"
    assertTrue (witness.run 5 == .done (.bool expected))
      s!"wordSgt {name} failed at the literal fuel boundary"

  let validBody : Expr := .binary .wordSgt (.word one) (.word zero)
  let wrongResult : Program := { resultType := .word, body := validBody }
  assertTrue (!wrongResult.check) "wordSgt accepted a word result type"

  let wrongLeft : Expr := .binary .wordSgt .unit (.word zero)
  let wrongRight : Expr := .binary .wordSgt (.word one) .unit
  assertTrue (!(boolProgram wrongLeft).check) "wordSgt accepted a non-word left"
  assertTrue (!(boolProgram wrongRight).check) "wordSgt accepted a non-word right"
  assertTrue
    ((boolProgram wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands .wordSgt .unit (.word zero)))
    "raw wordSgt did not expose its invalid left operand"
  assertTrue
    ((boolProgram wrongRight).run 5 ==
      .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "raw wordSgt did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let effectfulRight := allocatingWritingWord zero one Word.maximum
  let leftFault : Expr := .binary .wordSgt (.var 99) effectfulRight
  match (boolProgram leftFault).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordSgt evaluated right after a left fault"
  | result =>
      throw (IO.userError s!"wordSgt exposed the wrong left fault: {reprStr result}")

  let effectfulLeft := allocatingWritingWord zero one zero
  let rightFault : Expr := .binary .wordSgt effectfulLeft (.var 100)
  match (boolProgram rightFault).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordSgt right fault did not observe the left store"
  | result =>
      throw (IO.userError s!"wordSgt exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands : IO Unit := do
  let left := allocatingWritingWord zero one zero
  let right := allocatingWritingWord zero two Word.maximum
  let witness := boolProgram (.binary .wordSgt left right)
  assertTrue witness.check "effectful wordSgt failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordSgt finished below exact fuel"
  assertTrue
    (witness.runStateful 29 == .done (.bool true) [.word one, .word two])
    "wordSgt did not evaluate left then right exactly once or retain the store"

/-- Cover all eleven theorems plus signed values, types, faults, effects, and fuel. -/
def testCoreSignedComparison : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
