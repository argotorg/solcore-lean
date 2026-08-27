import Solcore.Core.ModularExponentiation
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for internal modular exponentiation. -/

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
private def thirtySeven : Word := word 37
private def highBit : Word := word (2 ^ 255)

example : Word.modularPowLoop 2 1 8 = (1 * 2 ^ 8) % wordModulus :=
  Word.modularPowLoop_correct 2 1 8
example : (thirtySeven.pow one).val =
    thirtySeven.val ^ one.val % wordModulus :=
  Word.pow_correct thirtySeven one
example : thirtySeven.pow zero = one := Word.pow_zero thirtySeven
example : thirtySeven.pow one = thirtySeven := Word.pow_one thirtySeven
example : one.pow Word.maximum = one := Word.one_pow Word.maximum
example : zero.pow one = zero := Word.zero_pow_of_positive one (by decide)
example : two.pow (word 256) = zero := Word.two_pow_256
example : Word.maximum.pow two = one := Word.maximum_pow_two

example : BinaryOp.wordPow.apply (.word thirtySeven) (.word one) =
    some (.word (thirtySeven.pow one)) :=
  BinaryOp.apply_wordPow thirtySeven one
example : Evaluates [] [] (.binary .wordPow (.word thirtySeven) (.word two))
    (.word (thirtySeven.pow two)) [] :=
  Evaluates.wordPow .word .word
example : Evaluates [] [] (.binary .wordPow (.word thirtySeven) (.word zero))
    (.word one) [] :=
  Evaluates.wordPow_exponent_zero .word .word
example : Evaluates [] [] (.binary .wordPow (.word thirtySeven) (.word one))
    (.word thirtySeven) [] :=
  Evaluates.wordPow_exponent_one .word .word
example : Evaluates [] [] (.binary .wordPow (.word one) (.word Word.maximum))
    (.word one) [] :=
  Evaluates.wordPow_one_base .word .word
example : Evaluates [] [] (.binary .wordPow (.word zero) (.word one))
    (.word zero) [] :=
  Evaluates.wordPow_zero_base_of_positive (by decide) .word .word

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
  -- Expected large-exponent values are algebraic boundaries, not giant Nat powers.
  let cases : List (String × Word × Word × Word) := [
    ("zero to zero", zero, zero, one),
    ("thirty-seven to zero", thirtySeven, zero, one),
    ("zero to one", zero, one, zero),
    ("one to maximum", one, Word.maximum, one),
    ("thirty-seven to one", thirtySeven, one, thirtySeven),
    ("two to eight", two, word 8, word 256),
    ("two to 256", two, word 256, zero),
    ("high bit squared", highBit, two, zero),
    ("maximum squared", Word.maximum, two, one),
    ("maximum to maximum", Word.maximum, Word.maximum, Word.maximum),
    ("two to maximum", two, Word.maximum, zero)
  ]
  for (name, base, exponent, expected) in cases do
    let witness := wordProgram (.binary .wordPow (.word base) (.word exponent))
    assertTrue witness.check s!"wordPow {name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordPow {name} finished below the literal fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"wordPow {name} failed at fuel five or charged its internal loop"

  let validBody : Expr := .binary .wordPow (.word thirtySeven) (.word two)
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordPow accepted a boolean result type"

  let wrongLeft : Expr := .binary .wordPow .unit (.word two)
  let wrongRight : Expr := .binary .wordPow (.word thirtySeven) .unit
  assertTrue (!(wordProgram wrongLeft).check) "wordPow accepted a non-word base"
  assertTrue (!(wordProgram wrongRight).check) "wordPow accepted a non-word exponent"
  assertTrue
    ((wordProgram wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands .wordPow .unit (.word two)))
    "raw wordPow did not expose its invalid left operand"
  assertTrue
    ((wordProgram wrongRight).run 5 ==
      .fault (.invalidBinaryOperands .wordPow (.word thirtySeven) .unit))
    "raw wordPow did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let effectfulExponent := allocatingWritingWord zero one two
  let baseFault : Expr := .binary .wordPow (.var 99) effectfulExponent
  match (wordProgram baseFault).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordPow evaluated exponent after a base fault"
  | result =>
      throw (IO.userError s!"wordPow exposed the wrong base fault: {reprStr result}")

  let effectfulBase := allocatingWritingWord zero one thirtySeven
  let exponentFault : Expr := .binary .wordPow effectfulBase (.var 100)
  match (wordProgram exponentFault).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordPow exponent fault did not observe the base effect"
  | result =>
      throw (IO.userError
        s!"wordPow exposed the wrong exponent fault: {reprStr result}")

private def testEffectfulOperands : IO Unit := do
  let base := allocatingWritingWord zero one thirtySeven
  let exponent := allocatingWritingWord zero two one
  let witness := wordProgram (.binary .wordPow base exponent)
  assertTrue witness.check "effectful wordPow failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordPow finished below exact fuel"
  assertTrue
    (witness.runStateful 29 ==
      .done (.word thirtySeven) [.word one, .word two])
    "wordPow did not evaluate base then exponent exactly once or retain the store"

/-- Cover all fourteen theorems plus values, types, faults, effects, store, and fuel. -/
def testCoreModularExponentiation : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
