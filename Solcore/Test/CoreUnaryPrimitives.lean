import Solcore.Core.UnaryPrimitives
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for direct unary primitives. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def zero : Word := Word.zero
private def one : Word := Word.ofNatModulo 1

example : zero.bitNot = Word.maximum := Word.bitNot_zero
example : Word.maximum.bitNot = zero := Word.bitNot_maximum
example (value : Word) : value.bitNot.bitNot = value :=
  Word.bitNot_involutive value

example : HasType [] (.unary .boolNot (.bool true)) .bool :=
  HasType.boolNot .bool

example : HasType [] (.unary .wordNot (.word zero)) .word :=
  HasType.wordNot .word

example : infer? [] (.unary .boolNot (.bool true)) = some .bool :=
  infer_boolNot rfl

example : infer? [] (.unary .wordNot (.word zero)) = some .word :=
  infer_wordNot rfl

example : Evaluates [] [] (.unary .boolNot (.bool true)) (.bool false) [] :=
  Evaluates.boolNot .bool

example : Evaluates [] [] (.unary .wordNot (.word one))
    (.word one.bitNot) [] :=
  Evaluates.wordNot .word

example : Evaluates [] [] (.unary .boolNot (.bool true)) (.bool false) [] :=
  Evaluates.boolNot_true .bool

example : Evaluates [] [] (.unary .boolNot (.bool false)) (.bool true) [] :=
  Evaluates.boolNot_false .bool

example : Evaluates [] [] (.unary .wordNot (.word zero))
    (.word Word.maximum) [] :=
  Evaluates.wordNot_zero .word

example : Evaluates [] [] (.unary .wordNot (.word Word.maximum))
    (.word zero) [] :=
  Evaluates.wordNot_maximum .word

example (operand : Expr) (mapping : Renaming) :
    (Expr.unary .boolNot operand).rename mapping =
      .unary .boolNot (operand.rename mapping) :=
  Expr.rename_boolNot operand mapping

example (operand : Expr) (mapping : Renaming) :
    (Expr.unary .wordNot operand).rename mapping =
      .unary .wordNot (operand.rename mapping) :=
  Expr.rename_wordNot operand mapping

example (operand : Expr) (cutoff : Nat) :
    (Expr.unary .boolNot operand).weakenAt cutoff =
      .unary .boolNot (operand.weakenAt cutoff) :=
  Expr.weakenAt_boolNot operand cutoff

example (operand : Expr) (cutoff : Nat) :
    (Expr.unary .wordNot operand).weakenAt cutoff =
      .unary .wordNot (operand.weakenAt cutoff) :=
  Expr.weakenAt_wordNot operand cutoff

private def program (resultType : Ty) (body : Expr) : Program := {
  resultType
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
  let boolCases : List (String × Program × Value) := [
    ("boolNot true", program .bool (.unary .boolNot (.bool true)), .bool false),
    ("boolNot false", program .bool (.unary .boolNot (.bool false)), .bool true)
  ]
  for (name, witness, expected) in boolCases do
    assertTrue witness.check s!"{name} failed to type-check"
    assertTrue (witness.run 2 == .outOfFuel)
      s!"{name} finished below the literal unary fuel boundary"
    assertTrue (witness.run 3 == .done expected)
      s!"{name} failed at the literal unary fuel boundary"

  let wordCases : List (String × Word × Word) := [
    ("zero", zero, Word.maximum),
    ("one", one, one.bitNot),
    ("maximum", Word.maximum, zero)
  ]
  for (name, input, expected) in wordCases do
    let witness := program .word (.unary .wordNot (.word input))
    assertTrue witness.check s!"wordNot {name} failed to type-check"
    assertTrue (witness.run 2 == .outOfFuel)
      s!"wordNot {name} finished below the literal unary fuel boundary"
    assertTrue (witness.run 3 == .done (.word expected))
      s!"wordNot {name} returned the wrong complement"
    let twice := program .word
      (.unary .wordNot (.unary .wordNot (.word input)))
    assertTrue (twice.run 5 == .done (.word input))
      s!"double wordNot did not recover {name}"

  assertTrue (!(program .word (.unary .boolNot (.bool true))).check)
    "boolNot was accepted with a word result type"
  assertTrue (!(program .bool (.unary .wordNot (.word zero))).check)
    "wordNot was accepted with a bool result type"
  assertTrue (!(program .bool (.unary .boolNot (.word zero))).check)
    "boolNot accepted a word operand"
  assertTrue (!(program .word (.unary .wordNot (.bool true))).check)
    "wordNot accepted a bool operand"

private def testRawFaults : IO Unit := do
  let badBool := program .bool (.unary .boolNot (.word zero))
  assertTrue
    (badBool.run 2 == .fault (.invalidUnaryOperand .boolNot (.word zero)))
    "raw boolNot did not expose its invalid word operand"
  let badWord := program .word (.unary .wordNot (.bool true))
  assertTrue
    (badWord.run 2 == .fault (.invalidUnaryOperand .wordNot (.bool true)))
    "raw wordNot did not expose its invalid bool operand"

private def testEffectfulWordNot : IO Unit := do
  let operand := allocatingWritingWord zero one zero
  let witness := program .word (.unary .wordNot operand)
  assertTrue witness.check "effectful wordNot failed to type-check"
  assertTrue (witness.run 14 == .outOfFuel)
    "effectful wordNot finished below its exact fuel boundary"
  assertTrue
    (witness.runStateful 15 == .done (.word Word.maximum) [.word one])
    "wordNot did not evaluate its operand exactly once or retain its final store"

/-- Cover every named unary theorem plus values, types, faults, effects, and fuel. -/
def testCoreUnaryPrimitives : IO Unit := do
  testValuesTypesAndLiteralFuel
  testRawFaults
  testEffectfulWordNot

end Tests
