import Solcore.Core.Derived
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused regressions for derived signed less/greater-than-or-equal. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Word := Word.ofNatModulo value
private def zero : Word := Word.zero
private def one : Word := word 1
private def highBit : Word := word (2 ^ 255)
private def positiveMaximum : Word := word (2 ^ 255 - 1)

example : Expr.wordSle (.word zero) (.word one) =
    .unary .boolNot (.binary .wordSgt (.word zero) (.word one)) :=
  Expr.wordSle_expansion (.word zero) (.word one)
example : Expr.wordSge (.word one) (.word zero) =
    .unary .boolNot (Expr.wordSlt (.word one) (.word zero)) :=
  Expr.wordSge_expansion (.word one) (.word zero)
example : HasType [] (Expr.wordSle (.word zero) (.word one)) .bool :=
  HasType.wordSle .word .word
example : HasType [] (Expr.wordSge (.word one) (.word zero)) .bool :=
  HasType.wordSge .word .word
example : infer? [] (Expr.wordSle (.word zero) (.word one)) = some .bool :=
  infer_wordSle rfl rfl
example : infer? [] (Expr.wordSge (.word one) (.word zero)) = some .bool :=
  infer_wordSge rfl rfl
example (left right : Expr) (mapping : Renaming) :
    (left.wordSle right).rename mapping =
      (left.rename mapping).wordSle (right.rename mapping) :=
  Expr.rename_wordSle left right mapping
example (left right : Expr) (mapping : Renaming) :
    (left.wordSge right).rename mapping =
      (left.rename mapping).wordSge (right.rename mapping) :=
  Expr.rename_wordSge left right mapping
example (left right : Expr) (cutoff : Nat) :
    (left.wordSle right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSle (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSle left right cutoff
example (left right : Expr) (cutoff : Nat) :
    (left.wordSge right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSge (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSge left right cutoff

example : Evaluates [] [] (Expr.wordSle (.word zero) (.word one))
    (.bool (!zero.signedGt one)) [] :=
  Evaluates.wordSle .word .word
example : Evaluates [] [] (Expr.wordSle (.word zero) (.word one)) (.bool true) [] :=
  Evaluates.wordSle_both_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSle (.word highBit) (.word Word.maximum)) (.bool true) [] :=
  Evaluates.wordSle_both_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSle (.word zero) (.word Word.maximum)) (.bool false) [] :=
  Evaluates.wordSle_nonnegative_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSle (.word Word.maximum) (.word zero)) (.bool true) [] :=
  Evaluates.wordSle_negative_nonnegative (by decide) (by decide) .word .word

example : Evaluates [] [] (Expr.wordSge (.word one) (.word zero))
    (.bool (!zero.signedGt one)) [] :=
  Evaluates.wordSge (definitions := []) .word .word .word .word .nil .nil .nil
example : Evaluates [] [] (Expr.wordSge (.word one) (.word zero)) (.bool true) [] :=
  Evaluates.wordSge_both_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSge (.word Word.maximum) (.word highBit)) (.bool true) [] :=
  Evaluates.wordSge_both_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSge (.word zero) (.word Word.maximum)) (.bool true) [] :=
  Evaluates.wordSge_nonnegative_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSge (.word Word.maximum) (.word zero)) (.bool false) [] :=
  Evaluates.wordSge_negative_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil

private def boolProgram (body : Expr) : Program := { resultType := .bool, body }

private def allocatingWritingWord (initial written result : Word) : Expr :=
  .letE (.newCell .word (.word initial))
    (.letE (.storeCell (.var 0) (.word written)) (.word result))

private def testValuesTypesAndFuel : IO Unit := do
  let cases : List (String × Word × Word × Bool × Bool) := [
    ("zero one", zero, one, true, false),
    ("one zero", one, zero, false, true),
    ("positive maximum zero", positiveMaximum, zero, false, true),
    ("zero positive maximum", zero, positiveMaximum, true, false),
    ("maximum high bit", Word.maximum, highBit, false, true),
    ("high bit maximum", highBit, Word.maximum, true, false),
    ("zero maximum", zero, Word.maximum, false, true),
    ("maximum zero", Word.maximum, zero, true, false),
    ("maximum equal", Word.maximum, Word.maximum, true, true)
  ]
  for (name, left, right, sleExpected, sgeExpected) in cases do
    let sle := boolProgram (Expr.wordSle (.word left) (.word right))
    let sge := boolProgram (Expr.wordSge (.word left) (.word right))
    assertTrue (sle.check && sge.check) s!"non-strict {name} failed to type-check"
    assertTrue (sle.run 6 == .outOfFuel && sle.run 7 == .done (.bool sleExpected))
      s!"wordSle {name} missed exact 6/7 fuel"
    assertTrue (sge.run 12 == .outOfFuel && sge.run 13 == .done (.bool sgeExpected))
      s!"wordSge {name} missed exact 12/13 fuel"

  for body in [Expr.wordSle .unit (.word zero), Expr.wordSle (.word one) .unit,
      Expr.wordSge .unit (.word zero), Expr.wordSge (.word one) .unit] do
    assertTrue (!(boolProgram body).check) "non-strict comparison accepted bad operand"
  let wrongSle : Program := {
    resultType := .word
    body := Expr.wordSle (.word zero) (.word one)
  }
  let wrongSge : Program := {
    resultType := .word
    body := Expr.wordSge (.word one) (.word zero)
  }
  assertTrue (!wrongSle.check && !wrongSge.check) "non-strict accepted word result"

  assertTrue ((boolProgram (Expr.wordSle .unit (.word one))).run 7 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "wordSle source-left payload was not direct"
  assertTrue ((boolProgram (Expr.wordSle (.word one) .unit)).run 7 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSle source-right payload was not direct"
  assertTrue ((boolProgram (Expr.wordSge .unit (.word one))).run 13 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSge source-left payload was not swapped"
  assertTrue ((boolProgram (Expr.wordSge (.word one) .unit)).run 13 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "wordSge source-right payload was not swapped"

private def testFaultOrder : IO Unit := do
  let effectfulRight := allocatingWritingWord zero one Word.maximum
  for (name, body) in [("sle", Expr.wordSle (.var 99) effectfulRight),
      ("sge", Expr.wordSge (.var 99) effectfulRight)] do
    match (boolProgram body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty s!"{name} evaluated right after left fault"
    | result => throw (IO.userError s!"{name} wrong left fault: {reprStr result}")

  let effectfulLeft := allocatingWritingWord zero one Word.maximum
  match (boolProgram (Expr.wordSle effectfulLeft (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one]) "sle right fault lost left store"
  | result => throw (IO.userError s!"sle wrong right fault: {reprStr result}")
  match (boolProgram (Expr.wordSge effectfulLeft (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 101) state =>
      assertTrue (state.store == [.word one]) "sge right fault lost left store"
  | result => throw (IO.userError s!"sge wrong weakened fault: {reprStr result}")

private def testEffects : IO Unit := do
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero (word 2) zero
  let sle := boolProgram (Expr.wordSle left right)
  let sge := boolProgram (Expr.wordSge left right)
  assertTrue (sle.run 30 == .outOfFuel &&
    sle.runStateful 31 == .done (.bool true) [.word one, .word (word 2)])
    "wordSle missed exact effect/store boundary"
  assertTrue (sge.run 36 == .outOfFuel &&
    sge.runStateful 37 == .done (.bool false) [.word one, .word (word 2)])
    "wordSge missed exact effect/store boundary"

/-- Cover all twenty theorems plus truth tables, types, faults, effects, and fuel. -/
def testCoreDerivedSignedNonStrictComparisons : IO Unit := do
  testValuesTypesAndFuel
  testFaultOrder
  testEffects

end Tests
