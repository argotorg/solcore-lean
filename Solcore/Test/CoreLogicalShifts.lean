import Solcore.Core.LogicalShifts
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for bounded logical word shifts. -/

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
private def six : Word := Word.ofNatModulo 6
private def eight : Word := Word.ofNatModulo 8
private def sixteen : Word := Word.ofNatModulo 16
private def shift255 : Word := Word.ofNatModulo 255
private def shift256 : Word := Word.ofNatModulo 256
private def highBit : Word := Word.ofNatModulo (2 ^ 255)

example : one.shiftLeft zero = one := Word.shiftLeft_zero one
example : Word.maximum.shiftRight zero = Word.maximum :=
  Word.shiftRight_zero Word.maximum
example : one.shiftLeft three = one <<< three :=
  Word.shiftLeft_of_lt_256 one three (by decide)
example : Word.maximum.shiftRight three = Word.maximum >>> three :=
  Word.shiftRight_of_lt_256 Word.maximum three (by decide)
example : one.shiftLeft shift256 = zero :=
  Word.shiftLeft_of_ge_256 one shift256 (by decide)
example : Word.maximum.shiftRight Word.maximum = zero :=
  Word.shiftRight_of_ge_256 Word.maximum Word.maximum (by decide)

example : BinaryOp.wordShl.apply (.word one) (.word three) =
    some (.word (one.shiftLeft three)) :=
  BinaryOp.apply_wordShl one three
example : BinaryOp.wordShr.apply (.word eight) (.word one) =
    some (.word (eight.shiftRight one)) :=
  BinaryOp.apply_wordShr eight one

example : Evaluates [] [] (.binary .wordShl (.word one) (.word three))
    (.word (one.shiftLeft three)) [] :=
  Evaluates.wordShl .word .word
example : Evaluates [] [] (.binary .wordShl (.word one) (.word three))
    (.word (one <<< three)) [] :=
  Evaluates.wordShl_lt_256 (by decide) .word .word
example : Evaluates [] [] (.binary .wordShl (.word one) (.word shift256))
    (.word zero) [] :=
  Evaluates.wordShl_ge_256 (by decide) .word .word
example : Evaluates [] [] (.binary .wordShr (.word eight) (.word one))
    (.word (eight.shiftRight one)) [] :=
  Evaluates.wordShr .word .word
example : Evaluates [] [] (.binary .wordShr (.word eight) (.word one))
    (.word (eight >>> one)) [] :=
  Evaluates.wordShr_lt_256 (by decide) .word .word
example : Evaluates [] []
    (.binary .wordShr (.word Word.maximum) (.word Word.maximum))
    (.word zero) [] :=
  Evaluates.wordShr_ge_256 (by decide) .word .word

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
    ("one shl three", .wordShl, one, three, eight),
    ("three shl one", .wordShl, three, one, six),
    ("eight shr one", .wordShr, eight, one, four),
    ("one shr eight", .wordShr, one, eight, zero),
    ("maximum shl zero", .wordShl, Word.maximum, zero, Word.maximum),
    ("maximum shr zero", .wordShr, Word.maximum, zero, Word.maximum),
    ("one shl 255", .wordShl, one, shift255, highBit),
    ("maximum shr 255", .wordShr, Word.maximum, shift255, one),
    ("one shl 256", .wordShl, one, shift256, zero),
    ("maximum shr 256", .wordShr, Word.maximum, shift256, zero),
    ("zero shl maximum", .wordShl, zero, Word.maximum, zero),
    ("zero shr maximum", .wordShr, zero, Word.maximum, zero)
  ]
  for (name, op, value, shift, expected) in cases do
    let witness := wordProgram (.binary op (.word value) (.word shift))
    assertTrue witness.check s!"{name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"{name} failed at the literal binary fuel boundary"

  for op in [BinaryOp.wordShl, .wordShr] do
    for body in [
        Expr.binary op .unit (.word one),
        Expr.binary op (.word one) .unit
      ] do
      assertTrue (!(wordProgram body).check)
        s!"{reprStr op} accepted a non-word operand: {reprStr body}"

    let body := Expr.binary op (.word one) (.word three)
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
  let rightWithEffect := allocatingWritingWord zero one shift256
  for op in [BinaryOp.wordShl, .wordShr] do
    let body := Expr.binary op (.var 99) rightWithEffect
    match (wordProgram body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated its shift after a value fault"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord zero one eight
  for op in [BinaryOp.wordShl, .wordShr] do
    let body := Expr.binary op leftWithEffect (.var 100)
    match (wordProgram body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one])
          s!"{reprStr op} shift fault did not observe the value store"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands : IO Unit := do
  let cases : List (String × BinaryOp × Word × Word × Word) := [
    ("wordShl in range", .wordShl, eight, one, sixteen),
    ("wordShr in range", .wordShr, eight, one, four),
    ("wordShl oversized", .wordShl, one, shift256, zero),
    ("wordShr oversized", .wordShr, Word.maximum, shift256, zero)
  ]
  for (name, op, value, shift, expected) in cases do
    let left := allocatingWritingWord zero one value
    let right := allocatingWritingWord zero two shift
    let witness := wordProgram (.binary op left right)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.word expected) [.word one, .word two])
      s!"{name} did not evaluate value then shift exactly once"

/-- Cover all fourteen theorems plus values, order, faults, effects, and fuel. -/
def testCoreLogicalShifts : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
