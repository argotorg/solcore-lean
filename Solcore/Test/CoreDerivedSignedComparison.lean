import Solcore.Core.DerivedSignedComparisonEval
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for effect-safe derived signed less-than. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def word (value : Nat) : Word := Word.ofNatModulo value
private def zero : Word := Word.zero
private def one : Word := word 1
private def highBit : Word := word (2 ^ 255)
private def positiveMaximum : Word := word (2 ^ 255 - 1)

example : Expr.wordSlt (.word zero) (.word one) =
    .letE (.word zero)
      (.letE ((.word one : Expr).weakenAt 0)
        (.binary .wordSgt (.var 0) (.var 1))) :=
  Expr.wordSlt_expansion (.word zero) (.word one)
example : HasType [] (Expr.wordSlt (.word zero) (.word one)) .bool :=
  HasType.wordSlt .word .word
example : infer? [] (Expr.wordSlt (.word zero) (.word one)) = some .bool :=
  infer_wordSlt rfl rfl
example (left right : Expr) (mapping : Renaming) :
    (left.wordSlt right).rename mapping =
      (left.rename mapping).wordSlt (right.rename mapping) :=
  Expr.rename_wordSlt left right mapping
example (left right : Expr) (cutoff : Nat) :
    (left.wordSlt right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSlt (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSlt left right cutoff

example : Evaluates [] [] (Expr.wordSlt (.word zero) (.word one))
    (.bool (one.signedGt zero)) [] :=
  Evaluates.wordSlt (definitions := [])
    .word .word .word .word .nil .nil
example : Evaluates [] [] (Expr.wordSlt (.word zero) (.word one))
    (.bool true) [] :=
  Evaluates.wordSlt_both_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil
example : Evaluates [] [] (Expr.wordSlt (.word highBit) (.word Word.maximum))
    (.bool true) [] :=
  Evaluates.wordSlt_both_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil
example : Evaluates [] [] (Expr.wordSlt (.word zero) (.word Word.maximum))
    (.bool false) [] :=
  Evaluates.wordSlt_nonnegative_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil
example : Evaluates [] [] (Expr.wordSlt (.word Word.maximum) (.word zero))
    (.bool true) [] :=
  Evaluates.wordSlt_negative_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil

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

private def testValuesTypesAndFuel : IO Unit := do
  let cases : List (String × Word × Word × Bool) := [
    ("zero below one", zero, one, true),
    ("one below zero", one, zero, false),
    ("zero below positive maximum", zero, positiveMaximum, true),
    ("positive maximum below zero", positiveMaximum, zero, false),
    ("high bit below maximum", highBit, Word.maximum, true),
    ("maximum below high bit", Word.maximum, highBit, false),
    ("zero below maximum", zero, Word.maximum, false),
    ("maximum below zero", Word.maximum, zero, true),
    ("maximum below maximum", Word.maximum, Word.maximum, false)
  ]
  for (name, left, right, expected) in cases do
    let witness := boolProgram (Expr.wordSlt (.word left) (.word right))
    assertTrue witness.check s!"wordSlt {name} failed to type-check as bool"
    assertTrue (witness.run 10 == .outOfFuel)
      s!"wordSlt {name} finished below exact literal fuel"
    assertTrue (witness.run 11 == .done (.bool expected))
      s!"wordSlt {name} failed at exact literal fuel"

  let validBody := Expr.wordSlt (.word zero) (.word one)
  let wrongResult : Program := { resultType := .word, body := validBody }
  assertTrue (!wrongResult.check) "wordSlt accepted a word result type"
  assertTrue (!(boolProgram (Expr.wordSlt .unit (.word one))).check)
    "wordSlt accepted a non-word source-left operand"
  assertTrue (!(boolProgram (Expr.wordSlt (.word zero) .unit)).check)
    "wordSlt accepted a non-word source-right operand"

  assertTrue
    ((boolProgram (Expr.wordSlt .unit (.word one))).run 11 ==
      .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSlt did not expose swapped bound values for invalid source-left"
  assertTrue
    ((boolProgram (Expr.wordSlt (.word zero) .unit)).run 11 ==
      .fault (.invalidBinaryOperands .wordSgt .unit (.word zero)))
    "wordSlt did not expose swapped bound values for invalid source-right"

private def testFaultOrder : IO Unit := do
  let effectfulRight := allocatingWritingWord zero one Word.maximum
  let leftFault := boolProgram (Expr.wordSlt (.var 99) effectfulRight)
  match leftFault.runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordSlt evaluated source-right after a source-left fault"
  | result =>
      throw (IO.userError s!"wordSlt exposed the wrong left fault: {reprStr result}")

  let effectfulLeft := allocatingWritingWord zero one Word.maximum
  let rightFault := boolProgram (Expr.wordSlt effectfulLeft (.var 100))
  match rightFault.runStateful 64 with
  | .fault (.unboundVariable 101) state =>
      assertTrue (state.store == [.word one])
        "wordSlt source-right fault did not observe the left store"
  | result =>
      throw (IO.userError s!"wordSlt exposed the wrong right fault: {reprStr result}")

private def testEffectOrder : IO Unit := do
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero (word 2) zero
  let witness := boolProgram (Expr.wordSlt left right)
  assertTrue witness.check "effectful wordSlt failed to type-check"
  assertTrue (witness.run 34 == .outOfFuel)
    "effectful wordSlt finished below exact fuel"
  assertTrue
    (witness.runStateful 35 == .done (.bool true) [.word one, .word (word 2)])
    "wordSlt did not preserve source left-to-right effects and final store"

/-- Cover all ten theorems plus signed values, swapped faults, effects, and fuel. -/
def testCoreDerivedSignedComparison : IO Unit := do
  testValuesTypesAndFuel
  testFaultOrder
  testEffectOrder

end Tests
