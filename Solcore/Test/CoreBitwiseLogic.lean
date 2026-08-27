import Solcore.Core.BitwiseLogic
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for binary bitwise word logic. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def zero : Word := Word.zero
private def one : Word := Word.ofNatModulo 1
private def two : Word := Word.ofNatModulo 2
private def maskAA : Word := Word.ofNatModulo 0xAA
private def maskCC : Word := Word.ofNatModulo 0xCC
private def mask88 : Word := Word.ofNatModulo 0x88
private def maskEE : Word := Word.ofNatModulo 0xEE
private def mask66 : Word := Word.ofNatModulo 0x66

example : maskAA.bitAnd zero = zero := Word.bitAnd_zero maskAA
example : maskAA.bitAnd maskAA = maskAA := Word.bitAnd_self maskAA
example : maskAA.bitAnd maskCC = maskCC.bitAnd maskAA :=
  Word.bitAnd_comm maskAA maskCC
example : maskAA.bitOr zero = maskAA := Word.bitOr_zero maskAA
example : maskAA.bitOr maskAA = maskAA := Word.bitOr_self maskAA
example : maskAA.bitOr maskCC = maskCC.bitOr maskAA :=
  Word.bitOr_comm maskAA maskCC
example : maskAA.bitXor zero = maskAA := Word.bitXor_zero maskAA
example : maskAA.bitXor maskAA = zero := Word.bitXor_self maskAA
example : maskAA.bitXor maskCC = maskCC.bitXor maskAA :=
  Word.bitXor_comm maskAA maskCC

example : BinaryOp.wordAnd.apply (.word maskAA) (.word maskCC) =
    some (.word (maskAA.bitAnd maskCC)) :=
  BinaryOp.apply_wordAnd maskAA maskCC
example : BinaryOp.wordOr.apply (.word maskAA) (.word maskCC) =
    some (.word (maskAA.bitOr maskCC)) :=
  BinaryOp.apply_wordOr maskAA maskCC
example : BinaryOp.wordXor.apply (.word maskAA) (.word maskCC) =
    some (.word (maskAA.bitXor maskCC)) :=
  BinaryOp.apply_wordXor maskAA maskCC

example : Evaluates [] [] (.binary .wordAnd (.word maskAA) (.word maskCC))
    (.word (maskAA.bitAnd maskCC)) [] :=
  Evaluates.wordAnd .word .word
example : Evaluates [] [] (.binary .wordOr (.word maskAA) (.word maskCC))
    (.word (maskAA.bitOr maskCC)) [] :=
  Evaluates.wordOr .word .word
example : Evaluates [] [] (.binary .wordXor (.word maskAA) (.word maskCC))
    (.word (maskAA.bitXor maskCC)) [] :=
  Evaluates.wordXor .word .word

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
  let cases : List (String × BinaryOp × Word × Word × Word) := [
    ("AA and CC", .wordAnd, maskAA, maskCC, mask88),
    ("AA or CC", .wordOr, maskAA, maskCC, maskEE),
    ("AA xor CC", .wordXor, maskAA, maskCC, mask66),
    ("maximum and zero", .wordAnd, Word.maximum, zero, zero),
    ("maximum and self", .wordAnd, Word.maximum, Word.maximum, Word.maximum),
    ("maximum or zero", .wordOr, Word.maximum, zero, Word.maximum),
    ("zero or maximum", .wordOr, zero, Word.maximum, Word.maximum),
    ("maximum or self", .wordOr, Word.maximum, Word.maximum, Word.maximum),
    ("maximum xor zero", .wordXor, Word.maximum, zero, Word.maximum),
    ("maximum xor self", .wordXor, Word.maximum, Word.maximum, zero)
  ]
  for (name, op, left, right, expected) in cases do
    let witness := wordProgram (.binary op (.word left) (.word right))
    assertTrue witness.check s!"{name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"{name} failed at the literal binary fuel boundary"

  for op in [BinaryOp.wordAnd, .wordOr, .wordXor] do
    for body in [
        Expr.binary op .unit (.word maskCC),
        Expr.binary op (.word maskAA) .unit
      ] do
      assertTrue (!(wordProgram body).check)
        s!"{reprStr op} accepted a non-word operand: {reprStr body}"

    let body := Expr.binary op (.word maskAA) (.word maskCC)
    let wrongResult : Program := { resultType := .bool, body }
    assertTrue (!wrongResult.check)
      s!"{reprStr op} was accepted with a bool result"

    assertTrue
      ((wordProgram (.binary op .unit (.word maskCC))).run 5 ==
        .fault (.invalidBinaryOperands op .unit (.word maskCC)))
      s!"raw {reprStr op} did not expose its invalid left operand"
    assertTrue
      ((wordProgram (.binary op (.word maskAA) .unit)).run 5 ==
        .fault (.invalidBinaryOperands op (.word maskAA) .unit))
      s!"raw {reprStr op} did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let rightWithEffect := allocatingWritingWord zero one maskCC
  for op in [BinaryOp.wordAnd, .wordOr, .wordXor] do
    let body := Expr.binary op (.var 99) rightWithEffect
    match (wordProgram body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated its right operand after a left fault"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord zero one maskAA
  for op in [BinaryOp.wordAnd, .wordOr, .wordXor] do
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
    ("wordAnd", .wordAnd, mask88),
    ("wordOr", .wordOr, maskEE),
    ("wordXor", .wordXor, mask66)
  ]
  for (name, op, expected) in cases do
    let left := allocatingWritingWord zero one maskAA
    let right := allocatingWritingWord zero two maskCC
    let witness := wordProgram (.binary op left right)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.word expected) [.word one, .word two])
      s!"{name} did not evaluate left then right exactly once"

/-- Cover all fifteen theorems plus values, order, faults, effects, and fuel. -/
def testCoreBitwiseLogic : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
