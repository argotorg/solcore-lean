import Solcore.Core.DirectWordComparisons
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for direct boolean word comparisons. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def zero : Word := Word.zero
private def one : Word := Word.ofNatModulo 1
private def two : Word := Word.ofNatModulo 2

example : BinaryOp.wordEq.apply (.word one) (.word two) =
    some (.bool (one == two)) :=
  BinaryOp.apply_wordEq one two
example : BinaryOp.wordGt.apply (.word two) (.word one) =
    some (.bool (decide (two > one))) :=
  BinaryOp.apply_wordGt two one

example : Evaluates [] [] (.binary .wordEq (.word one) (.word two))
    (.bool (one == two)) [] :=
  Evaluates.wordEq .word .word
example : Evaluates [] [] (.binary .wordEq (.word one) (.word one))
    (.bool true) [] :=
  Evaluates.wordEq_eq rfl .word .word
example : Evaluates [] [] (.binary .wordEq (.word one) (.word two))
    (.bool false) [] :=
  Evaluates.wordEq_ne (by decide) .word .word
example : Evaluates [] [] (.binary .wordGt (.word two) (.word one))
    (.bool (decide (two > one))) [] :=
  Evaluates.wordGt .word .word
example : Evaluates [] [] (.binary .wordGt (.word two) (.word one))
    (.bool true) [] :=
  Evaluates.wordGt_gt (by decide) .word .word
example : Evaluates [] [] (.binary .wordGt (.word one) (.word two))
    (.bool false) [] :=
  Evaluates.wordGt_not_gt (by decide) .word .word

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
  let cases : List (String × BinaryOp × Word × Word × Bool) := [
    ("zero eq zero", .wordEq, zero, zero, true),
    ("maximum eq maximum", .wordEq, Word.maximum, Word.maximum, true),
    ("zero eq maximum", .wordEq, zero, Word.maximum, false),
    ("one eq two", .wordEq, one, two, false),
    ("maximum gt zero", .wordGt, Word.maximum, zero, true),
    ("two gt one", .wordGt, two, one, true),
    ("zero gt maximum", .wordGt, zero, Word.maximum, false),
    ("maximum gt maximum", .wordGt, Word.maximum, Word.maximum, false),
    ("one gt two", .wordGt, one, two, false)
  ]
  for (name, op, left, right, expected) in cases do
    let witness := boolProgram (.binary op (.word left) (.word right))
    assertTrue witness.check s!"{name} failed to type-check as bool"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done (.bool expected))
      s!"{name} failed at the literal binary fuel boundary"

  for op in [BinaryOp.wordEq, .wordGt] do
    for body in [
        Expr.binary op .unit (.word one),
        Expr.binary op (.word one) .unit
      ] do
      assertTrue (!(boolProgram body).check)
        s!"{reprStr op} accepted a non-word operand: {reprStr body}"

    let body := Expr.binary op (.word two) (.word one)
    let wrongResult : Program := { resultType := .word, body }
    assertTrue (!wrongResult.check)
      s!"{reprStr op} was accepted with a word result"

    assertTrue
      ((boolProgram (.binary op .unit (.word one))).run 5 ==
        .fault (.invalidBinaryOperands op .unit (.word one)))
      s!"raw {reprStr op} did not expose its invalid left operand"
    assertTrue
      ((boolProgram (.binary op (.word one) .unit)).run 5 ==
        .fault (.invalidBinaryOperands op (.word one) .unit))
      s!"raw {reprStr op} did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let rightWithEffect := allocatingWritingWord zero one zero
  for op in [BinaryOp.wordEq, .wordGt] do
    let body := Expr.binary op (.var 99) rightWithEffect
    match (boolProgram body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated its right operand after a left fault"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord zero one Word.maximum
  for op in [BinaryOp.wordEq, .wordGt] do
    let body := Expr.binary op leftWithEffect (.var 100)
    match (boolProgram body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one])
          s!"{reprStr op} right fault did not observe the left store"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands : IO Unit := do
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero two zero
  for (name, op, expected) in [
      ("wordEq", BinaryOp.wordEq, false),
      ("wordGt", BinaryOp.wordGt, true)
    ] do
    let witness := boolProgram (.binary op left right)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.bool expected) [.word one, .word two])
      s!"{name} did not evaluate left then right exactly once"

/-- Cover all eight theorems plus values, order, faults, effects, and fuel. -/
def testCoreDirectWordComparisons : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
