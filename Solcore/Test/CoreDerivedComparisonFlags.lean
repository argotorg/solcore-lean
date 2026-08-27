import Solcore.Core.Check
import Solcore.Core.DerivedComparisonFlagEval
import Solcore.Core.Machine

/-! Semantic regressions for the derived word-valued comparison flags. -/

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

private def zero : Word := Word.zero
private def one : Word := Word.ofNatModulo 1

example : HasType [] (Expr.wordNeFlag (.word zero) (.word one)) .word :=
  HasType.wordNeFlag .word .word

example : HasType [] (Expr.wordLtFlag (.word zero) (.word one)) .word :=
  HasType.wordLtFlag .word .word

example : HasType [] (Expr.wordLeFlag (.word zero) (.word one)) .word :=
  HasType.wordLeFlag .word .word

example : HasType [] (Expr.wordGeFlag (.word zero) (.word one)) .word :=
  HasType.wordGeFlag .word .word

example : infer? [] (Expr.wordNeFlag (.word zero) (.word one)) = some .word :=
  infer_wordNeFlag rfl rfl

example : infer? [] (Expr.wordLtFlag (.word zero) (.word one)) = some .word :=
  infer_wordLtFlag rfl rfl

example : infer? [] (Expr.wordLeFlag (.word zero) (.word one)) = some .word :=
  infer_wordLeFlag rfl rfl

example : infer? [] (Expr.wordGeFlag (.word zero) (.word one)) = some .word :=
  infer_wordGeFlag rfl rfl

example : Evaluates [] [] (Expr.wordNeFlag (.word zero) (.word one))
    (.word one) [] :=
  Evaluates.wordNeFlag_ne (by decide) .word .word

example : Evaluates [] [] (Expr.wordLtFlag (.word zero) (.word one))
    (.word one) [] :=
  Evaluates.wordLtFlag_lt (definitions := [])
    (by decide) .word .word .word .word .nil .nil

example : Evaluates [] [] (Expr.wordLeFlag (.word one) (.word zero))
    (.word zero) [] :=
  Evaluates.wordLeFlag_gt (by decide) .word .word

example : Evaluates [] [] (Expr.wordGeFlag (.word one) (.word zero))
    (.word one) [] :=
  Evaluates.wordGeFlag_not_lt (definitions := [])
    (by decide) .word .word .word .word .nil .nil

private def wordProgram (body : Expr) : Program := {
  resultType := .word
  body
}

private def boolProgram (body : Expr) : Program := {
  resultType := .bool
  body
}

private def testValuesTypesAndFuel : IO Unit := do
  let maximum := Word.maximum
  let cases : List (String × Program × Nat × Value) := [
    ("wordNeFlag false", wordProgram
      (Expr.wordNeFlag (.word maximum) (.word maximum)), 10, .word zero),
    ("wordNeFlag true", wordProgram
      (Expr.wordNeFlag (.word zero) (.word maximum)), 10, .word one),
    ("wordLtFlag true", wordProgram
      (Expr.wordLtFlag (.word zero) (.word maximum)), 14, .word one),
    ("wordLtFlag false", wordProgram
      (Expr.wordLtFlag (.word maximum) (.word zero)), 14, .word zero),
    ("wordLeFlag true", wordProgram
      (Expr.wordLeFlag (.word zero) (.word maximum)), 10, .word one),
    ("wordLeFlag false", wordProgram
      (Expr.wordLeFlag (.word maximum) (.word zero)), 10, .word zero),
    ("wordGeFlag true", wordProgram
      (Expr.wordGeFlag (.word maximum) (.word zero)), 16, .word one),
    ("wordGeFlag false", wordProgram
      (Expr.wordGeFlag (.word zero) (.word maximum)), 16, .word zero)
  ]
  for (name, program, exactFuel, expected) in cases do
    assertTrue program.check s!"{name} failed to type-check as word"
    assertTrue (program.run (exactFuel - 1) == .outOfFuel)
      s!"{name} finished below its exact fuel boundary"
    assertTrue (program.run exactFuel == .done expected)
      s!"{name} failed at its exact fuel boundary"

  for body in [
      Expr.wordNeFlag .unit (.word zero),
      Expr.wordNeFlag (.word zero) .unit,
      Expr.wordLtFlag .unit (.word zero),
      Expr.wordLtFlag (.word zero) .unit,
      Expr.wordLeFlag .unit (.word zero),
      Expr.wordLeFlag (.word zero) .unit,
      Expr.wordGeFlag .unit (.word zero),
      Expr.wordGeFlag (.word zero) .unit
    ] do
    assertTrue (!(wordProgram body).check)
      s!"comparison flag accepted a non-word operand: {reprStr body}"

private def testBooleanDistinction : IO Unit := do
  let maximum := Word.maximum
  for body in [
      Expr.wordNeFlag (.word zero) (.word maximum),
      Expr.wordLtFlag (.word zero) (.word maximum),
      Expr.wordLeFlag (.word maximum) (.word zero),
      Expr.wordGeFlag (.word maximum) (.word zero)
    ] do
    assertTrue (!(boolProgram body).check)
      s!"word-valued comparison flag was accepted as bool: {reprStr body}"
  let cases : List (String × Program × Value) := [
    ("wordNe", boolProgram (Expr.wordNe (.word zero) (.word maximum)), .bool true),
    ("wordLt", boolProgram (Expr.wordLt (.word zero) (.word maximum)), .bool true),
    ("wordLe", boolProgram (Expr.wordLe (.word maximum) (.word zero)), .bool false),
    ("wordGe", boolProgram (Expr.wordGe (.word maximum) (.word zero)), .bool true)
  ]
  for (name, program, expected) in cases do
    assertTrue program.check s!"existing {name} lost its bool type"
    assertTrue (program.run 20 == .done expected)
      s!"existing {name} lost its boolean value"

private def testFaultOrder : IO Unit := do
  let rightWithEffect := allocatingWritingWord zero one zero
  let leftFaults : List (String × Program) := [
    ("wordNeFlag", wordProgram (Expr.wordNeFlag (.var 99) rightWithEffect)),
    ("wordLtFlag", wordProgram (Expr.wordLtFlag (.var 99) rightWithEffect)),
    ("wordLeFlag", wordProgram (Expr.wordLeFlag (.var 99) rightWithEffect)),
    ("wordGeFlag", wordProgram (Expr.wordGeFlag (.var 99) rightWithEffect))
  ]
  for (name, program) in leftFaults do
    match program.runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{name} evaluated its right operand after a left fault"
    | result =>
        throw (IO.userError s!"{name} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord zero one Word.maximum
  let rightFaults : List (String × Nat × Program) := [
    ("wordNeFlag", 100, wordProgram (Expr.wordNeFlag leftWithEffect (.var 100))),
    ("wordLtFlag", 101, wordProgram (Expr.wordLtFlag leftWithEffect (.var 100))),
    ("wordLeFlag", 100, wordProgram (Expr.wordLeFlag leftWithEffect (.var 100))),
    ("wordGeFlag", 101, wordProgram (Expr.wordGeFlag leftWithEffect (.var 100)))
  ]
  for (name, expectedIndex, program) in rightFaults do
    match program.runStateful 64 with
    | .fault (.unboundVariable actualIndex) state =>
        assertTrue (actualIndex == expectedIndex)
          s!"{name} exposed unbound index {actualIndex}, expected {expectedIndex}"
        assertTrue (state.store == [.word one])
          s!"{name} right fault did not observe the completed left store"
    | result =>
        throw (IO.userError s!"{name} exposed the wrong right fault: {reprStr result}")

private def testEffectsAndExactFuel : IO Unit := do
  let two := Word.ofNatModulo 2
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero two zero
  let cases : List (String × Program × Nat × Value) := [
    ("wordNeFlag", wordProgram (Expr.wordNeFlag left right), 34, .word one),
    ("wordLtFlag", wordProgram (Expr.wordLtFlag left right), 38, .word zero),
    ("wordLeFlag", wordProgram (Expr.wordLeFlag left right), 34, .word zero),
    ("wordGeFlag", wordProgram (Expr.wordGeFlag left right), 40, .word one)
  ]
  for (name, program, exactFuel, expected) in cases do
    assertTrue program.check s!"effectful {name} failed to type-check"
    assertTrue (program.run exactFuel.pred == .outOfFuel)
      s!"effectful {name} finished below its exact fuel boundary"
    assertTrue
      (program.runStateful exactFuel ==
        .done expected [.word one, .word two])
      s!"{name} did not evaluate and write left then right exactly once"

/-- Cover proof APIs, values, types, fuel, faults, and effect order. -/
def testCoreDerivedComparisonFlags : IO Unit := do
  testValuesTypesAndFuel
  testBooleanDistinction
  testFaultOrder
  testEffectsAndExactFuel

end Tests
