import Solcore.Core.ModularArithmetic
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for modular word arithmetic. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def zero : Word := Word.zero
private def one : Word := Word.ofNatModulo 1
private def two : Word := Word.ofNatModulo 2
private def three : Word := Word.ofNatModulo 3
private def four : Word := Word.ofNatModulo 4
private def seven : Word := Word.ofNatModulo 7
private def ten : Word := Word.ofNatModulo 10
private def twentyOne : Word := Word.ofNatModulo 21

example : seven.add zero = seven := Word.add_zero seven
example : Word.maximum.add one = zero := Word.add_maximum_one
example : seven.sub zero = seven := Word.sub_zero seven
example : seven.sub seven = zero := Word.sub_self seven
example : zero.sub one = Word.maximum := Word.zero_sub_one
example : seven.mul zero = zero := Word.mul_zero seven
example : seven.mul one = seven := Word.mul_one seven
example : Word.maximum.mul two = Word.ofNatModulo (wordModulus - 2) :=
  Word.maximum_mul_two

example : BinaryOp.wordAdd.apply (.word seven) (.word three) =
    some (.word (seven.add three)) :=
  BinaryOp.apply_wordAdd seven three
example : BinaryOp.wordSub.apply (.word seven) (.word three) =
    some (.word (seven.sub three)) :=
  BinaryOp.apply_wordSub seven three
example : BinaryOp.wordMul.apply (.word seven) (.word three) =
    some (.word (seven.mul three)) :=
  BinaryOp.apply_wordMul seven three

example : Evaluates [] [] (.binary .wordAdd (.word seven) (.word three))
    (.word (seven.add three)) [] :=
  Evaluates.wordAdd .word .word
example : Evaluates [] [] (.binary .wordSub (.word seven) (.word three))
    (.word (seven.sub three)) [] :=
  Evaluates.wordSub .word .word
example : Evaluates [] [] (.binary .wordMul (.word seven) (.word three))
    (.word (seven.mul three)) [] :=
  Evaluates.wordMul .word .word

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
  let underflow := Word.ofNatModulo (wordModulus - 4)
  let doubledMaximum := Word.ofNatModulo (wordModulus - 2)
  let highBit := Word.ofNatModulo (2 ^ 255)
  let cases : List (String × BinaryOp × Word × Word × Word) := [
    ("seven add three", .wordAdd, seven, three, ten),
    ("seven sub three", .wordSub, seven, three, four),
    ("three sub seven", .wordSub, three, seven, underflow),
    ("seven mul three", .wordMul, seven, three, twentyOne),
    ("maximum add one", .wordAdd, Word.maximum, one, zero),
    ("zero sub one", .wordSub, zero, one, Word.maximum),
    ("maximum mul two", .wordMul, Word.maximum, two, doubledMaximum),
    ("zero add maximum", .wordAdd, zero, Word.maximum, Word.maximum),
    ("maximum sub maximum", .wordSub, Word.maximum, Word.maximum, zero),
    ("maximum mul zero", .wordMul, Word.maximum, zero, zero),
    ("high bit mul two", .wordMul, highBit, two, zero)
  ]
  for (name, op, left, right, expected) in cases do
    let witness := wordProgram (.binary op (.word left) (.word right))
    assertTrue witness.check s!"{name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"{name} failed at the literal binary fuel boundary"

  for op in [BinaryOp.wordAdd, .wordSub, .wordMul] do
    for body in [
        Expr.binary op .unit (.word one),
        Expr.binary op (.word one) .unit
      ] do
      assertTrue (!(wordProgram body).check)
        s!"{reprStr op} accepted a non-word operand: {reprStr body}"

    let body := Expr.binary op (.word seven) (.word three)
    let wrongResult : Program := { resultType := .bool, body }
    assertTrue (!wrongResult.check)
      s!"{reprStr op} was accepted with a bool result"

    assertTrue
      ((wordProgram (.binary op .unit (.word one))).run 5 ==
        .fault (.invalidBinaryOperands op .unit (.word one)))
      s!"raw {reprStr op} did not expose its invalid left operand"
    assertTrue
      ((wordProgram (.binary op (.word one) .unit)).run 5 ==
        .fault (.invalidBinaryOperands op (.word one) .unit))
      s!"raw {reprStr op} did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let rightWithEffect := allocatingWritingWord zero one three
  for op in [BinaryOp.wordAdd, .wordSub, .wordMul] do
    let body := Expr.binary op (.var 99) rightWithEffect
    match (wordProgram body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated its right operand after a left fault"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord zero one seven
  for op in [BinaryOp.wordAdd, .wordSub, .wordMul] do
    let body := Expr.binary op leftWithEffect (.var 100)
    match (wordProgram body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one])
          s!"{reprStr op} right fault did not observe the left store"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands : IO Unit := do
  let cases : List (String × BinaryOp × Word) := [
    ("wordAdd", .wordAdd, ten),
    ("wordSub", .wordSub, four),
    ("wordMul", .wordMul, twentyOne)
  ]
  for (name, op, expected) in cases do
    let left := allocatingWritingWord zero one seven
    let right := allocatingWritingWord zero two three
    let witness := wordProgram (.binary op left right)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.word expected) [.word one, .word two])
      s!"{name} did not evaluate left then right exactly once"

/-- Cover all fourteen theorems plus values, order, faults, effects, and fuel. -/
def testCoreModularArithmetic : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
