import Solcore.Core.TernaryModularArithmetic
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for ternary modular word arithmetic. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Word := Word.ofNatModulo value
private def zero : Word := Word.zero
private def one : Word := word 1
private def two : Word := word 2
private def three : Word := word 3
private def four : Word := word 4
private def five : Word := word 5
private def six : Word := word 6
private def seven : Word := word 7

example : seven.addMod three zero = zero := Word.addMod_zero seven three
example : seven.addMod three five =
    Word.ofNatModulo ((seven.val + three.val) % five.val) :=
  Word.addMod_nonzero seven three five (by decide)
example : seven.mulMod three zero = zero := Word.mulMod_zero seven three
example : seven.mulMod three five =
    Word.ofNatModulo ((seven.val * three.val) % five.val) :=
  Word.mulMod_nonzero seven three five (by decide)
example : Word.maximum.addMod one Word.maximum = one :=
  Word.addMod_no_prewrap
example : Word.maximum.mulMod Word.maximum Word.maximum = zero :=
  Word.mulMod_no_prewrap

example : TernaryOp.wordAddMod.apply
    (.word seven) (.word three) (.word five) =
    some (.word (seven.addMod three five)) :=
  TernaryOp.apply_wordAddMod seven three five
example : TernaryOp.wordMulMod.apply
    (.word seven) (.word three) (.word five) =
    some (.word (seven.mulMod three five)) :=
  TernaryOp.apply_wordMulMod seven three five

example : Evaluates [] []
    (.ternary .wordAddMod (.word seven) (.word three) (.word five))
    (.word (seven.addMod three five)) [] :=
  Evaluates.wordAddMod .word .word .word
example : Evaluates [] []
    (.ternary .wordAddMod (.word seven) (.word three) (.word zero))
    (.word zero) [] :=
  Evaluates.wordAddMod_zero .word .word .word
example : Evaluates [] []
    (.ternary .wordAddMod (.word seven) (.word three) (.word five))
    (.word (Word.ofNatModulo ((seven.val + three.val) % five.val))) [] :=
  Evaluates.wordAddMod_nonzero (by decide) .word .word .word
example : Evaluates [] []
    (.ternary .wordMulMod (.word seven) (.word three) (.word five))
    (.word (seven.mulMod three five)) [] :=
  Evaluates.wordMulMod .word .word .word
example : Evaluates [] []
    (.ternary .wordMulMod (.word seven) (.word three) (.word zero))
    (.word zero) [] :=
  Evaluates.wordMulMod_zero .word .word .word
example : Evaluates [] []
    (.ternary .wordMulMod (.word seven) (.word three) (.word five))
    (.word (Word.ofNatModulo ((seven.val * three.val) % five.val))) [] :=
  Evaluates.wordMulMod_nonzero (by decide) .word .word .word

private def wordProgram (body : Expr) : Program := { resultType := .word, body }

private def allocatingWritingWord (initial written result : Word) : Expr :=
  .letE (.newCell .word (.word initial))
    (.letE (.storeCell (.var 0) (.word written)) (.word result))

private def testValuesTypesAndLiteralFuel : IO Unit := do
  let cases : List (String × TernaryOp × Word × Word × Word × Word) := [
    ("ordinary addmod", .wordAddMod, seven, three, six, four),
    ("ordinary mulmod", .wordMulMod, seven, three, five, one),
    ("addmod modulus one", .wordAddMod, seven, three, one, zero),
    ("mulmod modulus one", .wordMulMod, seven, three, one, zero),
    ("addmod modulus zero", .wordAddMod, seven, three, zero, zero),
    ("mulmod modulus zero", .wordMulMod, seven, three, zero, zero),
    ("addmod without prewrap", .wordAddMod,
      Word.maximum, Word.maximum, Word.maximum, zero),
    ("mulmod without prewrap", .wordMulMod,
      Word.maximum, Word.maximum, Word.maximum, zero)
  ]
  for (name, op, first, second, modulus, expected) in cases do
    let witness := wordProgram
      (.ternary op (.word first) (.word second) (.word modulus))
    assertTrue witness.check s!"{name} failed to type-check"
    assertTrue (witness.run 6 == .outOfFuel)
      s!"{name} finished below the literal fuel boundary"
    assertTrue (witness.run 7 == .done (.word expected))
      s!"{name} failed at the literal fuel boundary"

  for op in [TernaryOp.wordAddMod, .wordMulMod] do
    let valid := Expr.ternary op (.word seven) (.word three) (.word five)
    let wrongResult : Program := { resultType := .bool, body := valid }
    assertTrue (!wrongResult.check)
      s!"{reprStr op} accepted a bool result type"

    let invalidCases : List
        (String × CheckPathStep × Expr × Value × Value × Value) := [
      ("first", .ternaryFirst, .ternary op .unit (.word one) (.word two),
        .unit, .word one, .word two),
      ("second", .ternarySecond, .ternary op (.word one) .unit (.word two),
        .word one, .unit, .word two),
      ("modulus", .ternaryThird, .ternary op (.word one) (.word two) .unit,
        .word one, .word two, .unit)
    ]
    for (position, pathStep, body, firstValue, secondValue, thirdValue) in
        invalidCases do
      let witness := wordProgram body
      assertTrue (!witness.check)
        s!"{reprStr op} accepted a non-word {position} operand"
      match witness.checkDetailed with
      | .error error =>
          assertTrue (error.path == [pathStep])
            s!"{reprStr op} reported the wrong {position} diagnostic path"
          assertTrue (error.data == .primitiveOperandTypeMismatch .word .unit)
            s!"{reprStr op} reported the wrong {position} diagnostic data"
      | .ok inferred => throw (IO.userError
          s!"invalid {reprStr op} unexpectedly inferred {reprStr inferred}")
      assertTrue (witness.run 5 == .outOfFuel)
        s!"invalid {reprStr op} faulted below its exact fuel boundary"
      assertTrue
        (witness.run 6 ==
          .fault (.invalidTernaryOperands op firstValue secondValue thirdValue))
        s!"raw {reprStr op} changed its invalid {position} payload"

private def testFaultOrder : IO Unit := do
  for op in [TernaryOp.wordAddMod, .wordMulMod] do
    let laterSecond := allocatingWritingWord zero two three
    let laterModulus := allocatingWritingWord zero three five
    match (wordProgram
        (.ternary op (.var 99) laterSecond laterModulus)).runStateful 64 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated operands after a first fault"
    | result => throw (IO.userError
        s!"{reprStr op} exposed the wrong first fault: {reprStr result}")

    let firstEffect := allocatingWritingWord zero one seven
    match (wordProgram
        (.ternary op firstEffect (.var 100) laterModulus)).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one])
          s!"{reprStr op} second fault lost or repeated the first effect"
    | result => throw (IO.userError
        s!"{reprStr op} exposed the wrong second fault: {reprStr result}")

    let secondEffect := allocatingWritingWord zero two three
    match (wordProgram
        (.ternary op firstEffect secondEffect (.var 101))).runStateful 64 with
    | .fault (.unboundVariable 101) state =>
        assertTrue (state.store == [.word one, .word two])
          s!"{reprStr op} modulus fault lost or repeated earlier effects"
    | result => throw (IO.userError
        s!"{reprStr op} exposed the wrong modulus fault: {reprStr result}")

private def testEffectfulZeroModulus : IO Unit := do
  let first := allocatingWritingWord zero one Word.maximum
  let second := allocatingWritingWord zero two Word.maximum
  let modulus := allocatingWritingWord zero three zero
  for op in [TernaryOp.wordAddMod, .wordMulMod] do
    let witness := wordProgram (.ternary op first second modulus)
    assertTrue witness.check s!"effectful {reprStr op} failed to type-check"
    assertTrue (witness.run 42 == .outOfFuel)
      s!"effectful {reprStr op} finished below exact fuel"
    assertTrue
      (witness.runStateful 43 ==
        .done (.word zero) [.word one, .word two, .word three])
      s!"{reprStr op} did not evaluate all operands once or retain the final store"

/-- Cover all fourteen theorems plus values, types, faults, effects, and fuel. -/
def testCoreTernaryModularArithmetic : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulZeroModulus

end Tests
