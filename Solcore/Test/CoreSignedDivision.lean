import Solcore.Core.SignedDivision
import Solcore.Core.Check
import Solcore.Core.Machine

/-! Focused proof and runtime regressions for signed division and modulo. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Word := Word.ofNatModulo value
private def neg (magnitude : Nat) : Word := word (wordModulus - magnitude)
private def zero : Word := Word.zero
private def one : Word := word 1
private def two : Word := word 2
private def three : Word := word 3
private def seven : Word := word 7
private def negativeOne : Word := Word.maximum
private def minimum : Word := word (2 ^ 255)

example : seven.sdiv zero = zero := Word.sdiv_zero seven
example : seven.sdiv three =
    Word.ofSignedMagnitude (seven.signedNegative != three.signedNegative)
      (seven.signedMagnitude / three.signedMagnitude) :=
  Word.sdiv_nonzero seven three (by decide)
example : seven.smod zero = zero := Word.smod_zero seven
example : seven.smod three =
    Word.ofSignedMagnitude seven.signedNegative
      (seven.signedMagnitude % three.signedMagnitude) :=
  Word.smod_nonzero seven three (by decide)
example : minimum.sdiv negativeOne = minimum :=
  Word.sdiv_minimum_negative_one
example : minimum.smod negativeOne = zero :=
  Word.smod_minimum_negative_one

example : BinaryOp.wordSdiv.apply (.word seven) (.word three) =
    some (.word (seven.sdiv three)) := BinaryOp.apply_wordSdiv seven three
example : BinaryOp.wordSmod.apply (.word seven) (.word three) =
    some (.word (seven.smod three)) := BinaryOp.apply_wordSmod seven three

example : Evaluates [] [] (.binary .wordSdiv (.word seven) (.word three))
    (.word (seven.sdiv three)) [] := Evaluates.wordSdiv .word .word
example : Evaluates [] [] (.binary .wordSdiv (.word seven) (.word zero))
    (.word zero) [] := Evaluates.wordSdiv_zero .word .word
example : Evaluates [] [] (.binary .wordSdiv (.word seven) (.word three))
    (.word (Word.ofSignedMagnitude false two.val)) [] :=
  Evaluates.wordSdiv_nonzero (by decide) .word .word
example : Evaluates [] [] (.binary .wordSmod (.word seven) (.word three))
    (.word (seven.smod three)) [] := Evaluates.wordSmod .word .word
example : Evaluates [] [] (.binary .wordSmod (.word seven) (.word zero))
    (.word zero) [] := Evaluates.wordSmod_zero .word .word
example : Evaluates [] [] (.binary .wordSmod (.word seven) (.word three))
    (.word (Word.ofSignedMagnitude false one.val)) [] :=
  Evaluates.wordSmod_nonzero (by decide) .word .word

private def wordProgram (body : Expr) : Program := { resultType := .word, body }

private def allocatingWritingWord (initial written result : Word) : Expr :=
  .letE (.newCell .word (.word initial))
    (.letE (.storeCell (.var 0) (.word written)) (.word result))

private def testValuesTypesAndFuel : IO Unit := do
  let negativeTwo := neg 2
  let negativeThree := neg 3
  let negativeSeven := neg 7
  let cases : List (String × BinaryOp × Word × Word × Word) := [
    ("7 / 3", .wordSdiv, seven, three, two),
    ("7 / -3", .wordSdiv, seven, negativeThree, negativeTwo),
    ("-7 / 3", .wordSdiv, negativeSeven, three, negativeTwo),
    ("-7 / -3", .wordSdiv, negativeSeven, negativeThree, two),
    ("7 % 3", .wordSmod, seven, three, one),
    ("7 % -3", .wordSmod, seven, negativeThree, one),
    ("-7 % 3", .wordSmod, negativeSeven, three, negativeOne),
    ("-7 % -3", .wordSmod, negativeSeven, negativeThree, negativeOne),
    ("zero numerator div", .wordSdiv, zero, three, zero),
    ("zero numerator mod", .wordSmod, zero, three, zero),
    ("zero divisor div", .wordSdiv, seven, zero, zero),
    ("zero divisor mod", .wordSmod, seven, zero, zero),
    ("zero div zero", .wordSdiv, zero, zero, zero),
    ("zero mod zero", .wordSmod, zero, zero, zero),
    ("minimum / -1", .wordSdiv, minimum, negativeOne, minimum),
    ("minimum % -1", .wordSmod, minimum, negativeOne, zero),
    ("minimum / 1", .wordSdiv, minimum, one, minimum),
    ("minimum % 1", .wordSmod, minimum, one, zero),
    ("-1 / minimum", .wordSdiv, negativeOne, minimum, zero),
    ("-1 % minimum", .wordSmod, negativeOne, minimum, negativeOne),
    ("equal magnitude negative/positive", .wordSdiv, negativeSeven, seven,
      negativeOne),
    ("equal magnitude positive/negative", .wordSdiv, seven, negativeSeven,
      negativeOne),
    ("equal magnitude remainder", .wordSmod, negativeSeven, seven, zero)
  ]
  for (name, operation, dividend, divisor, expected) in cases do
    let witness := wordProgram
      (.binary operation (.word dividend) (.word divisor))
    assertTrue witness.check s!"{name} failed to type-check"
    assertTrue (witness.run 4 == .outOfFuel) s!"{name} finished below fuel 5"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"{name} produced the wrong signed result"

  for operation in [BinaryOp.wordSdiv, BinaryOp.wordSmod] do
    let valid := Expr.binary operation (.word seven) (.word three)
    let wrongResult : Program := { resultType := .bool, body := valid }
    assertTrue (!wrongResult.check) "signed operation accepted bool result"
    let wrongLeft := Expr.binary operation .unit (.word one)
    let wrongRight := Expr.binary operation (.word one) .unit
    assertTrue (!(wordProgram wrongLeft).check) "accepted nonword dividend"
    assertTrue (!(wordProgram wrongRight).check) "accepted nonword divisor"
    assertTrue ((wordProgram wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands operation .unit (.word one)))
      "invalid dividend payload changed"
    assertTrue ((wordProgram wrongRight).run 5 ==
      .fault (.invalidBinaryOperands operation (.word one) .unit))
      "invalid divisor payload changed"

private def testFaultOrder : IO Unit := do
  let rightEffect := allocatingWritingWord zero one three
  for operation in [BinaryOp.wordSdiv, BinaryOp.wordSmod] do
    match (wordProgram (.binary operation (.var 99) rightEffect)).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty "divisor ran after dividend fault"
    | result => throw (IO.userError s!"wrong dividend fault: {reprStr result}")

  let leftEffect := allocatingWritingWord zero one seven
  for operation in [BinaryOp.wordSdiv, BinaryOp.wordSmod] do
    match (wordProgram (.binary operation leftEffect (.var 100))).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one])
          "divisor fault lost completed dividend store"
    | result => throw (IO.userError s!"wrong divisor fault: {reprStr result}")

private def testEffects : IO Unit := do
  let dividend := allocatingWritingWord zero one (neg 7)
  for (name, operation, divisorResult, expected) in [
      ("nonzero sdiv", BinaryOp.wordSdiv, three, neg 2),
      ("nonzero smod", BinaryOp.wordSmod, three, negativeOne),
      ("zero sdiv", BinaryOp.wordSdiv, zero, zero),
      ("zero smod", BinaryOp.wordSmod, zero, zero) ] do
    let divisor := allocatingWritingWord zero two divisorResult
    let witness := wordProgram (.binary operation dividend divisor)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel) s!"{name} finished below fuel 29"
    assertTrue (witness.runStateful 29 ==
      .done (.word expected) [.word one, .word two])
      s!"{name} did not evaluate dividend then divisor exactly once"

/-- Cover all fourteen theorems plus signed values, faults, effects, and fuel. -/
def testCoreSignedDivision : IO Unit := do
  testValuesTypesAndFuel
  testFaultOrder
  testEffects

end Tests
