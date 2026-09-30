import Solcore.Core.Derived
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for signed word comparison flags. -/

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

example : Expr.wordSgtFlag (.word one) (.word zero) =
    (Expr.binary .wordSgt (.word one) (.word zero)).boolToWord :=
  Expr.wordSgtFlag_expansion (.word one) (.word zero)
example : Expr.wordSltFlag (.word zero) (.word one) =
    (Expr.wordSlt (.word zero) (.word one)).boolToWord :=
  Expr.wordSltFlag_expansion (.word zero) (.word one)
example : HasType [] (Expr.wordSgtFlag (.word one) (.word zero)) .word :=
  HasType.wordSgtFlag .word .word
example : HasType [] (Expr.wordSltFlag (.word zero) (.word one)) .word :=
  HasType.wordSltFlag .word .word
example : infer? [] (Expr.wordSgtFlag (.word one) (.word zero)) = some .word :=
  infer_wordSgtFlag rfl rfl
example : infer? [] (Expr.wordSltFlag (.word zero) (.word one)) = some .word :=
  infer_wordSltFlag rfl rfl
example (left right : Expr) (mapping : Renaming) :
    (left.wordSgtFlag right).rename mapping =
      (left.rename mapping).wordSgtFlag (right.rename mapping) :=
  Expr.rename_wordSgtFlag left right mapping
example (left right : Expr) (mapping : Renaming) :
    (left.wordSltFlag right).rename mapping =
      (left.rename mapping).wordSltFlag (right.rename mapping) :=
  Expr.rename_wordSltFlag left right mapping
example (left right : Expr) (cutoff : Nat) :
    (left.wordSgtFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSgtFlag (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSgtFlag left right cutoff
example (left right : Expr) (cutoff : Nat) :
    (left.wordSltFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSltFlag (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSltFlag left right cutoff

example : Evaluates [] [] (Expr.wordSgtFlag (.word one) (.word zero))
    (.word (if one.signedGt zero then one else zero)) [] :=
  Evaluates.wordSgtFlag .word .word
example : Evaluates [] [] (Expr.wordSgtFlag (.word one) (.word zero)) (.word one) [] :=
  Evaluates.wordSgtFlag_both_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSgtFlag (.word Word.maximum) (.word highBit)) (.word one) [] :=
  Evaluates.wordSgtFlag_both_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSgtFlag (.word zero) (.word Word.maximum)) (.word one) [] :=
  Evaluates.wordSgtFlag_nonnegative_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSgtFlag (.word Word.maximum) (.word zero)) (.word zero) [] :=
  Evaluates.wordSgtFlag_negative_nonnegative (by decide) (by decide) .word .word

example : Evaluates [] [] (Expr.wordSltFlag (.word zero) (.word one))
    (.word (if one.signedGt zero then one else zero)) [] :=
  Evaluates.wordSltFlag (definitions := []) .word .word .word .word .nil .nil .nil
example : Evaluates [] [] (Expr.wordSltFlag (.word zero) (.word one)) (.word one) [] :=
  Evaluates.wordSltFlag_both_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSltFlag (.word highBit) (.word Word.maximum)) (.word one) [] :=
  Evaluates.wordSltFlag_both_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSltFlag (.word zero) (.word Word.maximum)) (.word zero) [] :=
  Evaluates.wordSltFlag_nonnegative_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSltFlag (.word Word.maximum) (.word zero)) (.word one) [] :=
  Evaluates.wordSltFlag_negative_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil

private def wordProgram (body : Expr) : Program := { resultType := .word, body }

private def allocatingWritingWord (initial written result : Word) : Expr :=
  .letE (.newCell .word (.word initial))
    (.letE (.storeCell (.var 0) (.word written)) (.word result))

private def testValuesTypesAndFuel : IO Unit := do
  let cases : List (String × Word × Word × Word × Word) := [
    ("zero one", zero, one, zero, one),
    ("one zero", one, zero, one, zero),
    ("positive maximum zero", positiveMaximum, zero, one, zero),
    ("zero positive maximum", zero, positiveMaximum, zero, one),
    ("maximum high bit", Word.maximum, highBit, one, zero),
    ("high bit maximum", highBit, Word.maximum, zero, one),
    ("zero maximum", zero, Word.maximum, one, zero),
    ("maximum zero", Word.maximum, zero, zero, one),
    ("maximum equal", Word.maximum, Word.maximum, zero, zero)
  ]
  for (name, left, right, sgtExpected, sltExpected) in cases do
    let sgt := wordProgram (Expr.wordSgtFlag (.word left) (.word right))
    let slt := wordProgram (Expr.wordSltFlag (.word left) (.word right))
    assertTrue (sgt.check && slt.check) s!"signed flags {name} failed to type-check"
    assertTrue (sgt.run 7 == .outOfFuel && sgt.run 8 == .done (.word sgtExpected))
      s!"wordSgtFlag {name} missed exact 7/8 fuel"
    assertTrue (slt.run 13 == .outOfFuel && slt.run 14 == .done (.word sltExpected))
      s!"wordSltFlag {name} missed exact 13/14 fuel"

  for body in [Expr.wordSgtFlag .unit (.word zero),
      Expr.wordSgtFlag (.word one) .unit,
      Expr.wordSltFlag .unit (.word zero), Expr.wordSltFlag (.word one) .unit] do
    assertTrue (!(wordProgram body).check) "signed flag accepted a non-word operand"
  let wrongSgt : Program := {
    resultType := .bool
    body := Expr.wordSgtFlag (.word one) (.word zero)
  }
  let wrongSlt : Program := {
    resultType := .bool
    body := Expr.wordSltFlag (.word zero) (.word one)
  }
  assertTrue (!wrongSgt.check && !wrongSlt.check) "signed flag accepted bool result"

  assertTrue ((wordProgram (Expr.wordSgtFlag .unit (.word one))).run 8 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "wordSgtFlag invalid payload was not direct"
  assertTrue ((wordProgram (Expr.wordSltFlag .unit (.word one))).run 14 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSltFlag invalid payload was not swapped"
  assertTrue ((wordProgram (Expr.wordSgtFlag (.word one) .unit)).run 8 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSgtFlag invalid right payload was not direct"
  assertTrue ((wordProgram (Expr.wordSltFlag (.word one) .unit)).run 14 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "wordSltFlag invalid right payload was not swapped"

private def testFaultOrder : IO Unit := do
  let effectfulRight := allocatingWritingWord zero one Word.maximum
  for (name, body) in [("sgt", Expr.wordSgtFlag (.var 99) effectfulRight),
      ("slt", Expr.wordSltFlag (.var 99) effectfulRight)] do
    match (wordProgram body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty s!"{name} evaluated right after left fault"
    | result => throw (IO.userError s!"{name} wrong left fault: {reprStr result}")

  let effectfulLeft := allocatingWritingWord zero one Word.maximum
  let sgtRightFault := wordProgram (Expr.wordSgtFlag effectfulLeft (.var 100))
  let sltRightFault := wordProgram (Expr.wordSltFlag effectfulLeft (.var 100))
  match sgtRightFault.runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one]) "sgt right fault lost left store"
  | result => throw (IO.userError s!"sgt wrong right fault: {reprStr result}")
  match sltRightFault.runStateful 64 with
  | .fault (.unboundVariable 101) state =>
      assertTrue (state.store == [.word one]) "slt right fault lost left store"
  | result => throw (IO.userError s!"slt wrong weakened fault: {reprStr result}")

private def testEffects : IO Unit := do
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero (word 2) zero
  let sgt := wordProgram (Expr.wordSgtFlag left right)
  let slt := wordProgram (Expr.wordSltFlag left right)
  assertTrue (sgt.run 31 == .outOfFuel &&
    sgt.runStateful 32 == .done (.word zero) [.word one, .word (word 2)])
    "wordSgtFlag missed exact effect/store boundary"
  assertTrue (slt.run 37 == .outOfFuel &&
    slt.runStateful 38 == .done (.word one) [.word one, .word (word 2)])
    "wordSltFlag missed exact effect/store boundary"

/-- Cover all twenty theorems plus signed values, types, faults, effects, and fuel. -/
def testCoreSignedComparisonFlags : IO Unit := do
  testValuesTypesAndFuel
  testFaultOrder
  testEffects

end Tests
