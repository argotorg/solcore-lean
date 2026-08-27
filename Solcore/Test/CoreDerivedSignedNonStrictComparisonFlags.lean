import Solcore.Core.DerivedSignedNonStrictComparisonFlagEval
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Regressions for word-valued signed less/greater-than-or-equal builders. -/

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

example : Expr.wordSleFlag (.word zero) (.word one) =
    (Expr.wordSle (.word zero) (.word one)).boolToWord :=
  Expr.wordSleFlag_expansion (.word zero) (.word one)
example : Expr.wordSgeFlag (.word one) (.word zero) =
    (Expr.wordSge (.word one) (.word zero)).boolToWord :=
  Expr.wordSgeFlag_expansion (.word one) (.word zero)
example : HasType [] (Expr.wordSleFlag (.word zero) (.word one)) .word :=
  HasType.wordSleFlag .word .word
example : HasType [] (Expr.wordSgeFlag (.word one) (.word zero)) .word :=
  HasType.wordSgeFlag .word .word
example : infer? [] (Expr.wordSleFlag (.word zero) (.word one)) = some .word :=
  infer_wordSleFlag rfl rfl
example : infer? [] (Expr.wordSgeFlag (.word one) (.word zero)) = some .word :=
  infer_wordSgeFlag rfl rfl
example (left right : Expr) (mapping : Renaming) :
    (left.wordSleFlag right).rename mapping =
      (left.rename mapping).wordSleFlag (right.rename mapping) :=
  Expr.rename_wordSleFlag left right mapping
example (left right : Expr) (mapping : Renaming) :
    (left.wordSgeFlag right).rename mapping =
      (left.rename mapping).wordSgeFlag (right.rename mapping) :=
  Expr.rename_wordSgeFlag left right mapping
example (left right : Expr) (cutoff : Nat) :
    (left.wordSleFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSleFlag (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSleFlag left right cutoff
example (left right : Expr) (cutoff : Nat) :
    (left.wordSgeFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSgeFlag (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSgeFlag left right cutoff

example : Evaluates [] [] (Expr.wordSleFlag (.word zero) (.word one))
    (.word (if !zero.signedGt one then one else zero)) [] :=
  Evaluates.wordSleFlag .word .word
example : Evaluates [] [] (Expr.wordSleFlag (.word zero) (.word one))
    (.word one) [] :=
  Evaluates.wordSleFlag_both_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSleFlag (.word highBit) (.word Word.maximum)) (.word one) [] :=
  Evaluates.wordSleFlag_both_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSleFlag (.word zero) (.word Word.maximum)) (.word zero) [] :=
  Evaluates.wordSleFlag_nonnegative_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSleFlag (.word Word.maximum) (.word zero)) (.word one) [] :=
  Evaluates.wordSleFlag_negative_nonnegative (by decide) (by decide) .word .word

example : Evaluates [] [] (Expr.wordSgeFlag (.word one) (.word zero))
    (.word (if !zero.signedGt one then one else zero)) [] :=
  Evaluates.wordSgeFlag (definitions := []) .word .word .word .word .nil .nil
example : Evaluates [] [] (Expr.wordSgeFlag (.word one) (.word zero))
    (.word one) [] :=
  Evaluates.wordSgeFlag_both_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil
example : Evaluates [] []
    (Expr.wordSgeFlag (.word Word.maximum) (.word highBit)) (.word one) [] :=
  Evaluates.wordSgeFlag_both_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil
example : Evaluates [] []
    (Expr.wordSgeFlag (.word zero) (.word Word.maximum)) (.word one) [] :=
  Evaluates.wordSgeFlag_nonnegative_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil
example : Evaluates [] []
    (Expr.wordSgeFlag (.word Word.maximum) (.word zero)) (.word zero) [] :=
  Evaluates.wordSgeFlag_negative_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil

private def wordProgram (body : Expr) : Program := { resultType := .word, body }

private def allocatingWritingWord (initial written result : Word) : Expr :=
  .letE (.newCell .word (.word initial))
    (.letE (.storeCell (.var 0) (.word written)) (.word result))

private def testValuesTypesAndFuel : IO Unit := do
  let cases : List (String × Word × Word × Word × Word) := [
    ("zero one", zero, one, one, zero),
    ("one zero", one, zero, zero, one),
    ("positive max zero", positiveMaximum, zero, zero, one),
    ("zero positive max", zero, positiveMaximum, one, zero),
    ("maximum high bit", Word.maximum, highBit, zero, one),
    ("high bit maximum", highBit, Word.maximum, one, zero),
    ("zero maximum", zero, Word.maximum, zero, one),
    ("maximum zero", Word.maximum, zero, one, zero),
    ("zero equal", zero, zero, one, one),
    ("positive equal", positiveMaximum, positiveMaximum, one, one),
    ("negative equal", Word.maximum, Word.maximum, one, one)
  ]
  for (name, left, right, sleExpected, sgeExpected) in cases do
    let sle := wordProgram (Expr.wordSleFlag (.word left) (.word right))
    let sge := wordProgram (Expr.wordSgeFlag (.word left) (.word right))
    assertTrue (sle.check && sge.check) s!"{name} failed to type-check"
    assertTrue (sle.run 9 == .outOfFuel &&
      sle.run 10 == .done (.word sleExpected)) s!"SleFlag {name} fuel/value"
    assertTrue (sge.run 15 == .outOfFuel &&
      sge.run 16 == .done (.word sgeExpected)) s!"SgeFlag {name} fuel/value"

  for body in [Expr.wordSleFlag .unit (.word zero),
      Expr.wordSleFlag (.word one) .unit, Expr.wordSgeFlag .unit (.word zero),
      Expr.wordSgeFlag (.word one) .unit] do
    assertTrue (!(wordProgram body).check) "flag accepted nonword operand"
  for body in [Expr.wordSleFlag (.word zero) (.word one),
      Expr.wordSgeFlag (.word one) (.word zero)] do
    let wrong : Program := { resultType := .bool, body }
    assertTrue (!wrong.check) "word-valued flag accepted bool result"

  assertTrue ((wordProgram (Expr.wordSleFlag .unit (.word one))).run 10 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "SleFlag source-left payload was not direct"
  assertTrue ((wordProgram (Expr.wordSleFlag (.word one) .unit)).run 10 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "SleFlag source-right payload was not direct"
  assertTrue ((wordProgram (Expr.wordSgeFlag .unit (.word one))).run 16 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "SgeFlag source-left payload was not swapped"
  assertTrue ((wordProgram (Expr.wordSgeFlag (.word one) .unit)).run 16 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "SgeFlag source-right payload was not swapped"

private def testFaultOrder : IO Unit := do
  let rightEffect := allocatingWritingWord zero one Word.maximum
  for (name, body) in [("sle", Expr.wordSleFlag (.var 99) rightEffect),
      ("sge", Expr.wordSgeFlag (.var 99) rightEffect)] do
    match (wordProgram body).runStateful 12 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty s!"{name} evaluated right after left fault"
    | result => throw (IO.userError s!"{name} wrong left fault: {reprStr result}")

  let leftEffect := allocatingWritingWord zero one Word.maximum
  match (wordProgram (Expr.wordSleFlag leftEffect (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one]) "SleFlag lost left store"
  | result => throw (IO.userError s!"SleFlag wrong right fault: {reprStr result}")
  match (wordProgram (Expr.wordSgeFlag leftEffect (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 101) state =>
      assertTrue (state.store == [.word one]) "SgeFlag lost left store"
  | result => throw (IO.userError s!"SgeFlag wrong weakened fault: {reprStr result}")

private def testEffects : IO Unit := do
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero (word 2) zero
  let sle := wordProgram (Expr.wordSleFlag left right)
  let sge := wordProgram (Expr.wordSgeFlag left right)
  assertTrue (sle.run 33 == .outOfFuel &&
    sle.runStateful 34 == .done (.word one) [.word one, .word (word 2)])
    "SleFlag missed exact effect/store boundary"
  assertTrue (sge.run 39 == .outOfFuel &&
    sge.runStateful 40 == .done (.word zero) [.word one, .word (word 2)])
    "SgeFlag missed exact effect/store boundary"

/-- Cover twenty APIs plus canonical values, types, faults, effects, and fuel. -/
def testCoreDerivedSignedNonStrictComparisonFlags : IO Unit := do
  testValuesTypesAndFuel
  testFaultOrder
  testEffects

end Tests
