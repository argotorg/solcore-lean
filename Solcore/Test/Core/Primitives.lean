import Solcore.Core.ArithmeticShift
import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.BitwiseLogic
import Solcore.Core.ShortCircuit
import Solcore.Core.ByteSelection
import Solcore.Core.Derived
import Solcore.Core.CountLeadingZeros
import Solcore.Core.DirectWordComparisons
import Solcore.Core.BoundedSafety
import Solcore.Core.HostRunner
import Solcore.Core.LogicalShifts
import Solcore.Core.ModularArithmetic
import Solcore.Core.ModularExponentiation
import Solcore.Core.SignExtension
import Solcore.Core.SignedComparison
import Solcore.Core.SignedDivision
import Solcore.Core.TernaryModularArithmetic
import Solcore.Core.UnaryPrimitives
import Solcore.Core.UnsignedDivision

/-!
# Core primitive tests

Word, integer, boolean and byte primitives of Core: arithmetic, comparisons and their flags, shifts,
signed and modular operations, conversions, and the derived forms built from them.
-/

section
-- leanmerge: from Solcore.Test.CoreArithmeticShift
/-! Focused proof and runtime regressions for internal arithmetic right shift. -/

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
private def shift255 : Word := word 255
private def shift256 : Word := word 256
private def highBit : Word := word (2 ^ 255)
private def highBitShiftOne : Word := word (wordModulus - 2 ^ 254)
private def negativeTwo : Word := word (wordModulus - 2)
private def negativeThree : Word := word (wordModulus - 3)

example : highBit.shiftArithmeticRight zero = highBit :=
  Word.shiftArithmeticRight_zero highBit
example : (word 4).shiftArithmeticRight one = word (4 / 2 ^ one.val) :=
  Word.shiftArithmeticRight_of_lt_256_nonnegative (word 4) one
    (by decide) (by decide)
example : negativeThree.shiftArithmeticRight one =
    word (wordModulus - 1 -
      ((wordModulus - 1 - negativeThree.val) / 2 ^ one.val)) :=
  Word.shiftArithmeticRight_of_lt_256_negative negativeThree one
    (by decide) (by decide)
example : one.shiftArithmeticRight shift256 = zero :=
  Word.shiftArithmeticRight_of_ge_256_nonnegative one shift256
    (by decide) (by decide)
example : highBit.shiftArithmeticRight shift256 = Word.maximum :=
  Word.shiftArithmeticRight_of_ge_256_negative highBit shift256
    (by decide) (by decide)

example : BinaryOp.wordSar.apply (.word highBit) (.word one) =
    some (.word (highBit.shiftArithmeticRight one)) :=
  BinaryOp.apply_wordSar highBit one
example : Evaluates [] [] (.binary .wordSar (.word highBit) (.word one))
    (.word (highBit.shiftArithmeticRight one)) [] :=
  Evaluates.wordSar .word .word
example : Evaluates [] [] (.binary .wordSar (.word (word 4)) (.word one))
    (.word two) [] :=
  Evaluates.wordSar_lt_256_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSar (.word negativeTwo) (.word one))
    (.word Word.maximum) [] :=
  Evaluates.wordSar_lt_256_negative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSar (.word one) (.word shift256))
    (.word zero) [] :=
  Evaluates.wordSar_ge_256_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSar (.word highBit) (.word shift256))
    (.word Word.maximum) [] :=
  Evaluates.wordSar_ge_256_negative (by decide) (by decide) .word .word

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
  let cases : List (String × Word × Word × Word) := [
    ("positive four by one", word 4, one, two),
    ("high bit by zero", highBit, zero, highBit),
    ("high bit by one", highBit, one, highBitShiftOne),
    ("high bit by 255", highBit, shift255, Word.maximum),
    ("high bit by 256", highBit, shift256, Word.maximum),
    ("maximum by one", Word.maximum, one, Word.maximum),
    ("maximum by maximum shift", Word.maximum, Word.maximum, Word.maximum),
    ("negative two by one", negativeTwo, one, Word.maximum),
    ("negative three by one", negativeThree, one, negativeTwo),
    ("positive one by 255", one, shift255, zero),
    ("positive one by 256", one, shift256, zero),
    ("positive one by maximum shift", one, Word.maximum, zero)
  ]
  for (name, value, shift, expected) in cases do
    let witness := wordProgram (.binary .wordSar (.word value) (.word shift))
    assertTrue witness.check s!"wordSar {name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordSar {name} finished below the literal fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"wordSar {name} failed at the literal fuel boundary"

  let validBody : Expr := .binary .wordSar (.word highBit) (.word one)
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordSar accepted a boolean result type"

  let wrongLeft : Expr := .binary .wordSar .unit (.word one)
  let wrongRight : Expr := .binary .wordSar (.word highBit) .unit
  assertTrue (!(wordProgram wrongLeft).check) "wordSar accepted a non-word value"
  assertTrue (!(wordProgram wrongRight).check) "wordSar accepted a non-word shift"
  assertTrue
    ((wordProgram wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands .wordSar .unit (.word one)))
    "raw wordSar did not expose its invalid left operand"
  assertTrue
    ((wordProgram wrongRight).run 5 ==
      .fault (.invalidBinaryOperands .wordSar (.word highBit) .unit))
    "raw wordSar did not expose its invalid right operand"

private def testFaultOrder : IO Unit := do
  let effectfulShift := allocatingWritingWord zero one one
  let valueFault : Expr := .binary .wordSar (.var 99) effectfulShift
  match (wordProgram valueFault).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordSar evaluated shift after a value fault"
  | result =>
      throw (IO.userError s!"wordSar exposed the wrong value fault: {reprStr result}")

  let effectfulValue := allocatingWritingWord zero one highBit
  let shiftFault : Expr := .binary .wordSar effectfulValue (.var 100)
  match (wordProgram shiftFault).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordSar shift fault did not observe the value effect"
  | result =>
      throw (IO.userError s!"wordSar exposed the wrong shift fault: {reprStr result}")

private def testEffectfulOperands : IO Unit := do
  let value := allocatingWritingWord zero one highBit
  let shift := allocatingWritingWord zero two one
  let witness := wordProgram (.binary .wordSar value shift)
  assertTrue witness.check "effectful wordSar failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordSar finished below exact fuel"
  assertTrue
    (witness.runStateful 29 ==
      .done (.word highBitShiftOne) [.word one, .word two])
    "wordSar did not evaluate value then shift exactly once or retain the store"

/-- Cover all eleven theorems plus values, types, faults, effects, store, and fuel. -/
def testCoreArithmeticShift : IO Unit := do
  testValuesTypesAndLiteralFuel
  testFaultOrder
  testEffectfulOperands

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreBitwiseLogic
/-! Focused proof and runtime regressions for binary bitwise word logic. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def one_variant : Word := Word.ofNatModulo 1
private def two_variant : Word := Word.ofNatModulo 2
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

private def wordProgram_variant (body : Expr) : Program := {
  resultType := .word
  body
}

private def allocatingWritingWord_variant
    (initial written result : Word) : Expr :=
  .letE
    (.newCell .word (.word initial))
    (.letE
      (.storeCell (.var 0) (.word written))
      (.word result))

private def testValuesTypesAndLiteralFuel_variant : IO Unit := do
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
    let witness := wordProgram_variant (.binary op (.word left) (.word right))
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
      assertTrue (!(wordProgram_variant body).check)
        s!"{reprStr op} accepted a non-word operand: {reprStr body}"

    let body := Expr.binary op (.word maskAA) (.word maskCC)
    let wrongResult : Program := { resultType := .bool, body }
    assertTrue (!wrongResult.check)
      s!"{reprStr op} was accepted with a bool result"

    assertTrue
      ((wordProgram_variant (.binary op .unit (.word maskCC))).run 5 ==
        .fault (.invalidBinaryOperands op .unit (.word maskCC)))
      s!"raw {reprStr op} did not expose its invalid left operand"
    assertTrue
      ((wordProgram_variant (.binary op (.word maskAA) .unit)).run 5 ==
        .fault (.invalidBinaryOperands op (.word maskAA) .unit))
      s!"raw {reprStr op} did not expose its invalid right operand"

private def testFaultOrder_variant : IO Unit := do
  let rightWithEffect := allocatingWritingWord_variant zero one_variant maskCC
  for op in [BinaryOp.wordAnd, .wordOr, .wordXor] do
    let body := Expr.binary op (.var 99) rightWithEffect
    match (wordProgram_variant body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated its right operand after a left fault"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord_variant zero one_variant maskAA
  for op in [BinaryOp.wordAnd, .wordOr, .wordXor] do
    let body := Expr.binary op leftWithEffect (.var 100)
    match (wordProgram_variant body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one_variant])
          s!"{reprStr op} right fault did not observe the left store"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands_variant : IO Unit := do
  let cases : List (String × BinaryOp × Word) := [
    ("wordAnd", .wordAnd, mask88),
    ("wordOr", .wordOr, maskEE),
    ("wordXor", .wordXor, mask66)
  ]
  for (name, op, expected) in cases do
    let left := allocatingWritingWord_variant zero one_variant maskAA
    let right := allocatingWritingWord_variant zero two_variant maskCC
    let witness := wordProgram_variant (.binary op left right)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.word expected) [.word one_variant, .word two_variant])
      s!"{name} did not evaluate left then right exactly once"

/-- Cover all fifteen theorems plus values, order, faults, effects, and fuel. -/
def testCoreBitwiseLogic : IO Unit := do
  testValuesTypesAndLiteralFuel_variant
  testFaultOrder_variant
  testEffectfulOperands_variant

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreBooleanConnectives
/-! Executable regressions for the derived short-circuit boolean connectives. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def testTruthTables : IO Unit := do
  let cases : List (Bool × Bool × Bool × Bool) := [
    (false, false, false, false),
    (false, true, false, true),
    (true, false, false, true),
    (true, true, true, true)
  ]
  for (left, right, andResult, orResult) in cases do
    let andProgram : Program := {
      resultType := .bool
      body := Expr.boolAnd (.bool left) (.bool right)
    }
    let orProgram : Program := {
      resultType := .bool
      body := Expr.boolOr (.bool left) (.bool right)
    }
    assertTrue andProgram.check
      s!"boolAnd failed to type-check for {left}, {right}"
    assertTrue orProgram.check
      s!"boolOr failed to type-check for {left}, {right}"
    assertTrue (andProgram.run 4 == .done (.bool andResult))
      s!"boolAnd returned the wrong result for {left}, {right}"
    assertTrue (orProgram.run 4 == .done (.bool orResult))
      s!"boolOr returned the wrong result for {left}, {right}"

private def testTypesAndRawFaults : IO Unit := do
  let wrongAndCondition : Program := {
    resultType := .bool
    body := Expr.boolAnd .unit (.bool true)
  }
  let wrongOrCondition : Program := {
    resultType := .bool
    body := Expr.boolOr .unit (.bool false)
  }
  let wrongAndRight : Program := {
    resultType := .bool
    body := Expr.boolAnd (.bool true) .unit
  }
  let wrongOrRight : Program := {
    resultType := .bool
    body := Expr.boolOr (.bool false) .unit
  }
  assertTrue (!wrongAndCondition.check)
    "boolAnd must reject a non-boolean condition"
  assertTrue (!wrongOrCondition.check)
    "boolOr must reject a non-boolean condition"
  assertTrue (!wrongAndRight.check)
    "boolAnd must reject a non-boolean right operand"
  assertTrue (!wrongOrRight.check)
    "boolOr must reject a non-boolean right operand"
  assertTrue (wrongAndCondition.run 2 == .fault (.expectedBool .unit))
    "unchecked boolAnd must expose a non-boolean condition fault"
  assertTrue (wrongOrCondition.run 2 == .fault (.expectedBool .unit))
    "unchecked boolOr must expose a non-boolean condition fault"

  let skippedAndFault : Program := {
    resultType := .bool
    body := Expr.boolAnd (.bool false) (.var 99)
  }
  let selectedAndFault : Program := {
    resultType := .bool
    body := Expr.boolAnd (.bool true) (.var 99)
  }
  let skippedOrFault : Program := {
    resultType := .bool
    body := Expr.boolOr (.bool true) (.var 99)
  }
  let selectedOrFault : Program := {
    resultType := .bool
    body := Expr.boolOr (.bool false) (.var 99)
  }
  assertTrue (skippedAndFault.run 4 == .done (.bool false))
    "boolAnd false must skip a faulting right operand"
  assertTrue (selectedAndFault.run 3 == .fault (.unboundVariable 99))
    "boolAnd true must evaluate a faulting right operand"
  assertTrue (skippedOrFault.run 4 == .done (.bool true))
    "boolOr true must skip a faulting right operand"
  assertTrue (selectedOrFault.run 3 == .fault (.unboundVariable 99))
    "boolOr false must evaluate a faulting right operand"

private def testEffectsAndExactFuel : IO Unit := do
  let allocatingTrue : Expr :=
    .letE (.newCell .unit .unit) (.bool true)
  let allocatingFalse : Expr :=
    .letE (.newCell .unit .unit) (.bool false)
  let leftAllocatingFalse : Expr :=
    .letE (.newCell .bool (.bool true)) (.bool false)
  let leftAllocatingTrue : Expr :=
    .letE (.newCell .bool (.bool false)) (.bool true)
  let rightAllocatingFalse : Expr :=
    .letE (.newCell .word (.word Word.zero)) (.bool false)
  let allocatingAndWritingTrue : Expr :=
    .letE
      (.newCell .bool (.bool false))
      (.letE
        (.storeCell (.var 0) (.bool true))
        (.bool true))
  let andSkipped : Program := {
    resultType := .bool
    body := Expr.boolAnd (.bool false) allocatingTrue
  }
  let andSelected : Program := {
    resultType := .bool
    body := Expr.boolAnd (.bool true) allocatingFalse
  }
  let orSkipped : Program := {
    resultType := .bool
    body := Expr.boolOr (.bool true) allocatingFalse
  }
  let orSelected : Program := {
    resultType := .bool
    body := Expr.boolOr (.bool false) allocatingTrue
  }
  let effectfulLeftAndSkipped : Program := {
    resultType := .bool
    body := Expr.boolAnd leftAllocatingFalse allocatingTrue
  }
  let effectfulLeftOrSkipped : Program := {
    resultType := .bool
    body := Expr.boolOr leftAllocatingTrue allocatingFalse
  }
  let bothSelected : Program := {
    resultType := .bool
    body := Expr.boolAnd leftAllocatingTrue rightAllocatingFalse
  }
  let writeSkipped : Program := {
    resultType := .bool
    body := Expr.boolAnd (.bool false) allocatingAndWritingTrue
  }
  let writeSelected : Program := {
    resultType := .bool
    body := Expr.boolAnd (.bool true) allocatingAndWritingTrue
  }
  for program in [
      andSkipped, andSelected, orSkipped, orSelected,
      effectfulLeftAndSkipped, effectfulLeftOrSkipped, bothSelected,
      writeSkipped, writeSelected
    ] do
    assertTrue program.check
      s!"effectful connective failed to type-check: {reprStr program.body}"

  assertTrue (andSkipped.run 3 == .outOfFuel)
    "three transitions must be insufficient for skipped boolAnd"
  assertTrue (andSkipped.runStateful 4 == .done (.bool false) [])
    "boolAnd false must finish at four transitions without running its RHS"
  assertTrue (orSkipped.run 3 == .outOfFuel)
    "three transitions must be insufficient for skipped boolOr"
  assertTrue (orSkipped.runStateful 4 == .done (.bool true) [])
    "boolOr true must finish at four transitions without running its RHS"

  assertTrue (andSelected.run 8 == .outOfFuel)
    "eight transitions must be insufficient for selected boolAnd"
  assertTrue (andSelected.runStateful 9 == .done (.bool false) [.unit])
    "boolAnd true must run its RHS exactly once and preserve its store"
  assertTrue (orSelected.run 8 == .outOfFuel)
    "eight transitions must be insufficient for selected boolOr"
  assertTrue (orSelected.runStateful 9 == .done (.bool true) [.unit])
    "boolOr false must run its RHS exactly once and preserve its store"

  assertTrue (effectfulLeftAndSkipped.run 8 == .outOfFuel)
    "eight transitions must be insufficient for effectful-left boolAnd"
  assertTrue
    (effectfulLeftAndSkipped.runStateful 9 ==
      .done (.bool false) [.bool true])
    "boolAnd must preserve its left operand's store while skipping its RHS"
  assertTrue (effectfulLeftOrSkipped.run 8 == .outOfFuel)
    "eight transitions must be insufficient for effectful-left boolOr"
  assertTrue
    (effectfulLeftOrSkipped.runStateful 9 ==
      .done (.bool true) [.bool false])
    "boolOr must preserve its left operand's store while skipping its RHS"

  assertTrue (bothSelected.run 13 == .outOfFuel)
    "thirteen transitions must be insufficient when both operands have effects"
  assertTrue
    (bothSelected.runStateful 14 ==
      .done (.bool false) [.bool false, .word Word.zero])
    "the selected RHS must begin from and extend the left operand's store"

  assertTrue (writeSkipped.runStateful 4 == .done (.bool false) [])
    "short-circuiting must skip both allocation and write in the RHS"
  assertTrue (writeSelected.run 15 == .outOfFuel)
    "fifteen transitions must be insufficient for the allocating/writing RHS"
  assertTrue
    (writeSelected.runStateful 16 == .done (.bool true) [.bool true])
    "a selected RHS must expose its allocation followed by its storeCell write"

private def testWeakening : IO Unit := do
  let andExpr := Expr.boolAnd (.var 0) (.var 2)
  let weakenedAnd := Expr.boolAnd (.var 1) (.var 3)
  assertTrue (andExpr.weakenAt 0 == weakenedAnd)
    "boolAnd weakening must preserve both free-variable references"

  let orExpr := Expr.boolOr (.var 0) (.var 1)
  let weakenedOr := Expr.boolOr (.var 0) (.var 2)
  assertTrue (orExpr.weakenAt 1 == weakenedOr)
    "boolOr weakening must not capture either free-variable reference"

/-- Cover truth tables, faults, short-circuited effects, exact fuel, and weakening
for the derived boolean connectives. -/
def testCoreBooleanConnectives : IO Unit := do
  testTruthTables
  testTypesAndRawFaults
  testEffectsAndExactFuel
  testWeakening

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreByteSelection
/-! Focused proof and runtime regressions for internal word byte selection. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def value1122 : Word := word 0x1122

example : (word 30).byteAt value1122 = word 0x11 :=
  Word.byteAt_index30_1122
example : (word 31).byteAt value1122 = word 0x22 :=
  Word.byteAt_index31_1122
example : (word 0).byteAt zero = zero := Word.byteAt_zero (word 0)
example : (word 31).byteAt value1122 =
    word ((value1122.val / 2 ^ (8 * (31 - (word 31).val))) % 256) :=
  Word.byteAt_of_lt_32 (word 31) value1122 (by decide)
example : (word 32).byteAt value1122 = zero :=
  Word.byteAt_of_ge_32 (word 32) value1122 (by decide)

example : BinaryOp.wordByte.apply (.word (word 30)) (.word value1122) =
    some (.word ((word 30).byteAt value1122)) :=
  BinaryOp.apply_wordByte (word 30) value1122
example : Evaluates [] []
    (.binary .wordByte (.word (word 30)) (.word value1122))
    (.word ((word 30).byteAt value1122)) [] :=
  Evaluates.wordByte .word .word
example : Evaluates [] []
    (.binary .wordByte (.word (word 30)) (.word value1122))
    (.word (word 0x11)) [] :=
  Evaluates.wordByte_lt_32 (by decide) .word .word
example : Evaluates [] []
    (.binary .wordByte (.word (word 32)) (.word value1122))
    (.word zero) [] :=
  Evaluates.wordByte_ge_32 (by decide) .word .word

private def testValuesTypesAndLiteralFuel_variant2 : IO Unit := do
  let cases : List (String × Word × Word × Word) := [
    ("1122 index 0", word 0, value1122, zero),
    ("1122 index 29", word 29, value1122, zero),
    ("1122 index 30", word 30, value1122, word 0x11),
    ("1122 index 31", word 31, value1122, word 0x22),
    ("1122 index 32", word 32, value1122, zero),
    ("1122 maximum index", Word.maximum, value1122, zero),
    ("zero value index 0", word 0, zero, zero),
    ("zero value index 31", word 31, zero, zero),
    ("maximum value index 0", word 0, Word.maximum, word 0xff),
    ("maximum value index 31", word 31, Word.maximum, word 0xff)
  ]
  for (name, index, value, expected) in cases do
    let witness := wordProgram (.binary .wordByte (.word index) (.word value))
    assertTrue witness.check s!"wordByte {name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordByte {name} finished below the literal fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"wordByte {name} failed at the literal fuel boundary"

  let validBody : Expr := .binary .wordByte (.word (word 30)) (.word value1122)
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordByte accepted a boolean result type"

  let wrongLeft : Expr := .binary .wordByte .unit (.word value1122)
  let wrongRight : Expr := .binary .wordByte (.word (word 30)) .unit
  assertTrue (!(wordProgram wrongLeft).check) "wordByte accepted a non-word index"
  assertTrue (!(wordProgram wrongRight).check) "wordByte accepted a non-word value"
  assertTrue
    ((wordProgram wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands .wordByte .unit (.word value1122)))
    "raw wordByte did not expose its invalid left operand"
  assertTrue
    ((wordProgram wrongRight).run 5 ==
      .fault (.invalidBinaryOperands .wordByte (.word (word 30)) .unit))
    "raw wordByte did not expose its invalid right operand"

private def testFaultOrder_variant2 : IO Unit := do
  let effectfulValue := allocatingWritingWord zero one value1122
  let leftFault : Expr := .binary .wordByte (.var 99) effectfulValue
  match (wordProgram leftFault).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordByte evaluated its value operand after an index fault"
  | result =>
      throw (IO.userError s!"wordByte exposed the wrong index fault: {reprStr result}")

  let effectfulIndex := allocatingWritingWord zero one (word 30)
  let rightFault : Expr := .binary .wordByte effectfulIndex (.var 100)
  match (wordProgram rightFault).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordByte value fault did not observe the index effect"
  | result =>
      throw (IO.userError s!"wordByte exposed the wrong value fault: {reprStr result}")

private def testEffectfulOperands_variant2 : IO Unit := do
  let index := allocatingWritingWord zero one (word 30)
  let value := allocatingWritingWord zero two value1122
  let witness := wordProgram (.binary .wordByte index value)
  assertTrue witness.check "effectful wordByte failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordByte finished below exact fuel"
  assertTrue
    (witness.runStateful 29 == .done (.word (word 0x11)) [.word one, .word two])
    "wordByte did not evaluate index then value exactly once or retain the store"

/-- Cover all nine theorems plus values, types, faults, effects, store, and fuel. -/
def testCoreByteSelection : IO Unit := do
  testValuesTypesAndLiteralFuel_variant2
  testFaultOrder_variant2
  testEffectfulOperands_variant2

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreComparisonFlags
/-! Executable regressions for derived word-valued comparison flags. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def testValuesAndTypes : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let equalMaximum : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.word Word.maximum) (.word Word.maximum)
  }
  let unequalBoundary : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.word Word.zero) (.word Word.maximum)
  }
  let maximumGreater : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word Word.maximum) (.word Word.zero)
  }
  let zeroNotGreater : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word Word.zero) (.word Word.maximum)
  }
  let equalNotGreater : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word Word.maximum) (.word Word.maximum)
  }
  let ordinaryGreater : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word two) (.word one)
  }

  for program in [
      equalMaximum, unequalBoundary, maximumGreater, zeroNotGreater,
      equalNotGreater, ordinaryGreater
    ] do
    assertTrue program.check
      s!"comparison flag failed to type-check as word: {reprStr program.body}"

  assertTrue (equalMaximum.run 8 == .done (.word one))
    "wordEqFlag must map equal maximum words to one"
  assertTrue (unequalBoundary.run 8 == .done (.word Word.zero))
    "wordEqFlag must map unequal boundary words to zero"
  assertTrue (maximumGreater.run 8 == .done (.word one))
    "wordGtFlag must compare the maximum word above zero"
  assertTrue (zeroNotGreater.run 8 == .done (.word Word.zero))
    "wordGtFlag must not compare zero above the maximum word"
  assertTrue (equalNotGreater.run 8 == .done (.word Word.zero))
    "wordGtFlag must remain strict at the maximum-word boundary"
  assertTrue (ordinaryGreater.run 8 == .done (.word one))
    "wordGtFlag must use unsigned greater-than"

  let eqBadLeft : Program := {
    resultType := .word
    body := Expr.wordEqFlag .unit (.word Word.zero)
  }
  let eqBadRight : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.word Word.zero) .unit
  }
  let gtBadLeft : Program := {
    resultType := .word
    body := Expr.wordGtFlag .unit (.word Word.zero)
  }
  let gtBadRight : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word Word.zero) .unit
  }
  for program in [eqBadLeft, eqBadRight, gtBadLeft, gtBadRight] do
    assertTrue (!program.check)
      s!"comparison flag accepted a non-word operand: {reprStr program.body}"
  assertTrue
    (eqBadLeft.run 5 ==
      .fault (.invalidBinaryOperands .wordEq .unit (.word Word.zero)))
    "unchecked wordEqFlag must expose its invalid left operand"
  assertTrue
    (gtBadRight.run 5 ==
      .fault (.invalidBinaryOperands .wordGt (.word Word.zero) .unit))
    "unchecked wordGtFlag must expose its invalid right operand"

  let wrongEqResult : Program := {
    resultType := .bool
    body := Expr.wordEqFlag (.word Word.zero) (.word Word.zero)
  }
  let wrongGtResult : Program := {
    resultType := .bool
    body := Expr.wordGtFlag (.word one) (.word Word.zero)
  }
  assertTrue (!wrongEqResult.check)
    "wordEqFlag must retain its word result type"
  assertTrue (!wrongGtResult.check)
    "wordGtFlag must retain its word result type"

private def testRawFaultOrder : IO Unit := do
  let one := Word.ofNatModulo 1
  let rightWithEffect :=
    allocatingWritingWord_variant Word.zero one Word.zero
  let leftFault : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.var 99) rightWithEffect
  }
  match leftFault.runStateful 2 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "a left fault must prevent evaluation of the right operand"
  | result =>
      throw (IO.userError
        s!"wordEqFlag exposed the wrong left-first fault: {reprStr result}")

  let leftWithEffect :=
    allocatingWritingWord_variant Word.zero one Word.maximum
  let rightFault : Program := {
    resultType := .word
    body := Expr.wordGtFlag leftWithEffect (.var 100)
  }
  match rightFault.runStateful 16 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "the right fault must observe the left operand's completed store"
  | result =>
      throw (IO.userError
        s!"wordGtFlag exposed the wrong right-second fault: {reprStr result}")

private def testEffectsAndExactFuel_variant : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let literalEq : Program := {
    resultType := .word
    body := Expr.wordEqFlag (.word Word.zero) (.word Word.zero)
  }
  let literalGt : Program := {
    resultType := .word
    body := Expr.wordGtFlag (.word one) (.word Word.zero)
  }
  assertTrue (literalEq.run 7 == .outOfFuel)
    "seven transitions must be insufficient for wordEqFlag"
  assertTrue (literalEq.run 8 == .done (.word one))
    "wordEqFlag must finish at its eight-transition boundary"
  assertTrue (literalGt.run 7 == .outOfFuel)
    "seven transitions must be insufficient for wordGtFlag"
  assertTrue (literalGt.run 8 == .done (.word one))
    "wordGtFlag must finish at its eight-transition boundary"

  let left := allocatingWritingWord_variant Word.zero one Word.maximum
  let right := allocatingWritingWord_variant Word.zero two Word.zero
  let effectfulEq : Program := {
    resultType := .word
    body := Expr.wordEqFlag left right
  }
  let effectfulGt : Program := {
    resultType := .word
    body := Expr.wordGtFlag left right
  }
  for program in [effectfulEq, effectfulGt] do
    assertTrue program.check
      s!"effectful comparison flag failed to type-check: {reprStr program.body}"
    assertTrue (program.run 31 == .outOfFuel)
      "thirty-one transitions must be insufficient for effectful flags"

  assertTrue
    (effectfulEq.runStateful 32 ==
      .done (.word Word.zero) [.word one, .word two])
    "wordEqFlag must evaluate left then right exactly once and preserve the store"
  assertTrue
    (effectfulGt.runStateful 32 ==
      .done (.word one) [.word one, .word two])
    "wordGtFlag must evaluate left then right exactly once and preserve the store"

private def testBooleanCompatibility : IO Unit := do
  let boolEq : Program := {
    resultType := .bool
    body := .binary .wordEq (.word Word.maximum) (.word Word.maximum)
  }
  let boolGt : Program := {
    resultType := .bool
    body := .binary .wordGt (.word Word.maximum) (.word Word.zero)
  }
  assertTrue boolEq.check
    "the existing wordEq operation must remain boolean-valued"
  assertTrue boolGt.check
    "the existing wordGt operation must remain boolean-valued"
  assertTrue (boolEq.run 5 == .done (.bool true))
    "wordEq must retain its boolean result"
  assertTrue (boolGt.run 5 == .done (.bool true))
    "wordGt must retain its boolean result"

/-- Cover values, types, fault order, effects, fuel, and compatibility with the
boolean-valued comparison primitives. -/
def testCoreComparisonFlags : IO Unit := do
  testValuesAndTypes
  testRawFaultOrder
  testEffectsAndExactFuel_variant
  testBooleanCompatibility

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreConversions
/-! Executable regressions for the derived boolean/word conversions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def testConversionValuesAndTypes : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let falseProgram : Program := {
    resultType := .word
    body := Expr.boolToWord (.bool false)
  }
  let trueProgram : Program := {
    resultType := .word
    body := Expr.boolToWord (.bool true)
  }
  let zeroProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word Word.zero)
  }
  let oneProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word one)
  }
  let twoProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word two)
  }
  let maximumProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word Word.maximum)
  }

  for program in [
      falseProgram, trueProgram, zeroProgram, oneProgram, twoProgram,
      maximumProgram
    ] do
    assertTrue program.check
      s!"derived conversion failed to type-check: {reprStr program.body}"

  assertTrue (falseProgram.run 4 == .done (.word Word.zero))
    "boolToWord must convert false to zero"
  assertTrue (trueProgram.run 4 == .done (.word one))
    "boolToWord must convert true to one"
  assertTrue (zeroProgram.run 7 == .done (.bool false))
    "wordToBool must convert zero to false"
  assertTrue (oneProgram.run 7 == .done (.bool true))
    "wordToBool must convert one to true"
  assertTrue (twoProgram.run 7 == .done (.bool true))
    "wordToBool truthiness must remain distinct from strict ABI boolean decoding"
  assertTrue (maximumProgram.run 7 == .done (.bool true))
    "wordToBool must convert every nonzero word, including the maximum, to true"

  let wrongBoolInput : Program := {
    resultType := .word
    body := Expr.boolToWord .unit
  }
  let wrongWordInput : Program := {
    resultType := .bool
    body := Expr.wordToBool .unit
  }
  assertTrue (!wrongBoolInput.check)
    "boolToWord must reject a non-boolean operand"
  assertTrue (!wrongWordInput.check)
    "wordToBool must reject a non-word operand"
  assertTrue (wrongBoolInput.run 2 == .fault (.expectedBool .unit))
    "the unchecked boolToWord expansion must expose its boolean-shape fault"
  assertTrue
    (wrongWordInput.run 5 ==
      .fault (.invalidBinaryOperands .wordEq .unit (.word Word.zero)))
    "the unchecked wordToBool expansion must expose its word-comparison fault"

private def testExactFuelAndSingleEvaluation : IO Unit := do
  let one := Word.ofNatModulo 1
  let boolProgram : Program := {
    resultType := .word
    body := Expr.boolToWord (.bool true)
  }
  assertTrue (boolProgram.run 3 == .outOfFuel)
    "three transitions must be insufficient for boolToWord"
  assertTrue (boolProgram.run 4 == .done (.word one))
    "boolToWord must finish at its four-transition boundary"

  let wordProgram : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word Word.maximum)
  }
  assertTrue (wordProgram.run 6 == .outOfFuel)
    "six transitions must be insufficient for wordToBool"
  assertTrue (wordProgram.run 7 == .done (.bool true))
    "wordToBool must finish at its seven-transition boundary"

  let effectfulBool : Program := {
    resultType := .word
    body :=
      Expr.boolToWord
        (.letE (.newCell .unit .unit) (.bool true))
  }
  assertTrue effectfulBool.check
    "boolToWord must accept an effectful boolean operand"
  assertTrue
    (effectfulBool.runStateful 9 == .done (.word one) [.unit])
    "boolToWord must evaluate its operand exactly once before selecting the result"

  let effectfulWord : Program := {
    resultType := .bool
    body :=
      Expr.wordToBool
        (.letE (.newCell .unit .unit) (.word Word.maximum))
  }
  assertTrue effectfulWord.check
    "wordToBool must accept an effectful word operand"
  assertTrue
    (effectfulWord.runStateful 12 == .done (.bool true) [.unit])
    "wordToBool must evaluate its operand exactly once before comparison"

private def testWordIsZero : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let zeroProgram : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word Word.zero)
  }
  let oneProgram : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word one)
  }
  let twoProgram : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word two)
  }
  let maximumProgram : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word Word.maximum)
  }

  for program in [zeroProgram, oneProgram, twoProgram, maximumProgram] do
    assertTrue program.check
      s!"wordIsZero failed to type-check as word: {reprStr program.body}"

  assertTrue (zeroProgram.run 8 == .done (.word one))
    "wordIsZero must map zero to word one"
  assertTrue (oneProgram.run 8 == .done (.word Word.zero))
    "wordIsZero must map word one to word zero"
  assertTrue (twoProgram.run 8 == .done (.word Word.zero))
    "wordIsZero must map word two to word zero"
  assertTrue (maximumProgram.run 8 == .done (.word Word.zero))
    "wordIsZero must map the maximum word to word zero"

  let wrongInput : Program := {
    resultType := .word
    body := Expr.wordIsZero .unit
  }
  assertTrue (!wrongInput.check)
    "wordIsZero must reject a non-word operand"
  assertTrue
    (wrongInput.run 5 ==
      .fault (.invalidBinaryOperands .wordEq .unit (.word Word.zero)))
    "the unchecked wordIsZero expansion must expose its word-comparison fault"

  assertTrue (zeroProgram.run 7 == .outOfFuel)
    "seven transitions must be insufficient for wordIsZero"
  assertTrue (zeroProgram.run 8 == .done (.word one))
    "wordIsZero must finish at its eight-transition boundary"

  let effectfulProgram : Program := {
    resultType := .word
    body :=
      Expr.wordIsZero
        (.letE (.newCell .unit .unit) (.word Word.zero))
  }
  assertTrue effectfulProgram.check
    "wordIsZero must accept an effectful word operand"
  assertTrue
    (effectfulProgram.runStateful 13 == .done (.word one) [.unit])
    "wordIsZero must evaluate its operand exactly once before comparing with zero"

  let booleanTruthiness : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word Word.zero)
  }
  assertTrue booleanTruthiness.check
    "wordToBool must retain its boolean result type"
  assertTrue (booleanTruthiness.run 7 == .done (.bool false))
    "wordToBool zero must remain boolean false, distinct from wordIsZero's word one"
  let wrongDeclaredType : Program := {
    resultType := .bool
    body := Expr.wordIsZero (.word Word.zero)
  }
  assertTrue (!wrongDeclaredType.check)
    "wordIsZero must not be confused with the boolean-valued wordToBool helper"

private def testWordIsNonzero : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let zeroProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero (.word Word.zero)
  }
  let oneProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero (.word one)
  }
  let twoProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero (.word two)
  }
  let maximumProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero (.word Word.maximum)
  }

  for program in [zeroProgram, oneProgram, twoProgram, maximumProgram] do
    assertTrue program.check
      s!"wordIsNonzero failed to type-check as word: {reprStr program.body}"

  assertTrue (zeroProgram.run 10 == .done (.word Word.zero))
    "wordIsNonzero must map zero to word zero"
  assertTrue (oneProgram.run 10 == .done (.word one))
    "wordIsNonzero must map word one to word one"
  assertTrue (twoProgram.run 10 == .done (.word one))
    "wordIsNonzero must map word two to word one"
  assertTrue (maximumProgram.run 10 == .done (.word one))
    "wordIsNonzero must map the maximum word to word one"

  let wrongInput : Program := {
    resultType := .word
    body := Expr.wordIsNonzero .unit
  }
  let wrongDeclaredType : Program := {
    resultType := .bool
    body := Expr.wordIsNonzero (.word one)
  }
  assertTrue (!wrongInput.check)
    "wordIsNonzero must reject a non-word operand"
  assertTrue (!wrongDeclaredType.check)
    "wordIsNonzero must retain its word result type"
  assertTrue
    (wrongInput.run 6 ==
      .fault (.invalidBinaryOperands .wordEq .unit (.word Word.zero)))
    "the unchecked expansion must expose its inner word comparison fault"

  assertTrue (zeroProgram.run 9 == .outOfFuel)
    "nine transitions must be insufficient for canonical wordIsNonzero"
  assertTrue (zeroProgram.run 10 == .done (.word Word.zero))
    "canonical wordIsNonzero must finish at its ten-transition boundary"

  let effectfulOperand : Expr :=
    .letE
      (.newCell .word (.word Word.zero))
      (.letE
        (.storeCell (.var 0) (.word Word.maximum))
        (.word one))
  let effectfulProgram : Program := {
    resultType := .word
    body := Expr.wordIsNonzero effectfulOperand
  }
  assertTrue effectfulProgram.check
    "wordIsNonzero must accept an allocating and writing word operand"
  assertTrue
    (effectfulProgram.runStateful 22 ==
      .done (.word one) [.word Word.maximum])
    "wordIsNonzero must evaluate its operand once and preserve its updated store"

  let booleanTruthiness : Program := {
    resultType := .bool
    body := Expr.wordToBool (.word one)
  }
  let zeroPredicate : Program := {
    resultType := .word
    body := Expr.wordIsZero (.word one)
  }
  assertTrue (booleanTruthiness.run 7 == .done (.bool true))
    "wordToBool must remain boolean-valued"
  assertTrue (zeroPredicate.run 8 == .done (.word Word.zero))
    "wordIsZero must remain the inverse word-valued predicate"
  assertTrue (oneProgram.run 10 == .done (.word one))
    "wordIsNonzero must remain distinct from wordToBool and wordIsZero"

/-- Cover truth conversion and the word-valued zero/nonzero predicates, including
typing, raw faults, evaluation order, and exact fuel. -/
def testCoreConversions : IO Unit := do
  testConversionValuesAndTypes
  testExactFuelAndSingleEvaluation
  testWordIsZero
  testWordIsNonzero

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreCountLeadingZeros
/-! Focused proof and runtime regressions for internal word count-leading-zeros. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def highBit_variant : Word := Word.ofNatModulo (2 ^ 255)
private def count256 : Word := Word.ofNatModulo 256
private def count255 : Word := Word.ofNatModulo 255
private def count254 : Word := Word.ofNatModulo 254

example : zero.clz = count256 := Word.clz_zero
example (value : Word) (nonzero : value.val ≠ 0) :
    value.clz = Word.ofNatModulo (255 - Nat.log2 value.val) :=
  Word.clz_nonzero value nonzero
example : one_variant.clz = count255 := Word.clz_one
example : highBit_variant.clz = zero := Word.clz_highBit
example : Word.maximum.clz = zero := Word.clz_maximum

example : UnaryOp.wordClz.apply (.word two_variant) = some (.word two_variant.clz) :=
  UnaryOp.apply_wordClz two_variant
example : Evaluates [] [] (.unary .wordClz (.word two_variant)) (.word two_variant.clz) [] :=
  Evaluates.wordClz .word
example : Evaluates [] [] (.unary .wordClz (.word zero))
    (.word count256) [] :=
  Evaluates.wordClz_zero .word
example : Evaluates [] [] (.unary .wordClz (.word one_variant))
    (.word count255) [] :=
  Evaluates.wordClz_one .word
example : Evaluates [] [] (.unary .wordClz (.word highBit_variant)) (.word zero) [] :=
  Evaluates.wordClz_highBit .word
example : Evaluates [] [] (.unary .wordClz (.word Word.maximum))
    (.word zero) [] :=
  Evaluates.wordClz_maximum .word

private def testValuesTypesAndLiteralFuel_variant3 : IO Unit := do
  let cases : List (String × Word × Word) := [
    ("zero", zero, count256),
    ("one", one_variant, count255),
    ("two", two_variant, count254),
    ("high bit", highBit_variant, zero),
    ("maximum", Word.maximum, zero)
  ]
  for (name, input, expected) in cases do
    let witness := wordProgram_variant (.unary .wordClz (.word input))
    assertTrue witness.check s!"wordClz {name} failed to type-check as word"
    assertTrue (witness.run 2 == .outOfFuel)
      s!"wordClz {name} finished below the literal fuel boundary"
    assertTrue (witness.run 3 == .done (.word expected))
      s!"wordClz {name} failed at the literal fuel boundary"

  let validBody : Expr := .unary .wordClz (.word two_variant)
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordClz accepted a boolean result type"

  let wrongOperand : Expr := .unary .wordClz (.bool true)
  assertTrue (!(wordProgram_variant wrongOperand).check)
    "wordClz accepted a boolean operand"
  assertTrue
    ((wordProgram_variant wrongOperand).run 2 ==
      .fault (.invalidUnaryOperand .wordClz (.bool true)))
    "raw wordClz did not expose its invalid boolean operand"

private def testEffectfulOperand : IO Unit := do
  let operand := allocatingWritingWord_variant zero one_variant highBit_variant
  let witness := wordProgram_variant (.unary .wordClz operand)
  assertTrue witness.check "effectful wordClz failed to type-check"
  assertTrue (witness.run 14 == .outOfFuel)
    "effectful wordClz finished below exact fuel"
  assertTrue
    (witness.runStateful 15 == .done (.word zero) [.word one_variant])
    "wordClz did not evaluate its operand exactly once or retain the final store"

/-- Cover all eleven theorems plus values, types, fault, effect, store, and fuel. -/
def testCoreCountLeadingZeros : IO Unit := do
  testValuesTypesAndLiteralFuel_variant3
  testEffectfulOperand

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreDerivedComparisonFlags
/-! Semantic regressions for the derived word-valued comparison flags. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def one_variant2 : Word := Word.ofNatModulo 1

example : HasType [] (Expr.wordNeFlag (.word zero) (.word one_variant2)) .word :=
  HasType.wordNeFlag .word .word

example : HasType [] (Expr.wordLtFlag (.word zero) (.word one_variant2)) .word :=
  HasType.wordLtFlag .word .word

example : HasType [] (Expr.wordLeFlag (.word zero) (.word one_variant2)) .word :=
  HasType.wordLeFlag .word .word

example : HasType [] (Expr.wordGeFlag (.word zero) (.word one_variant2)) .word :=
  HasType.wordGeFlag .word .word

example : infer? [] (Expr.wordNeFlag (.word zero) (.word one_variant2)) = some .word :=
  infer_wordNeFlag rfl rfl

example : infer? [] (Expr.wordLtFlag (.word zero) (.word one_variant2)) = some .word :=
  infer_wordLtFlag rfl rfl

example : infer? [] (Expr.wordLeFlag (.word zero) (.word one_variant2)) = some .word :=
  infer_wordLeFlag rfl rfl

example : infer? [] (Expr.wordGeFlag (.word zero) (.word one_variant2)) = some .word :=
  infer_wordGeFlag rfl rfl

example : Evaluates [] [] (Expr.wordNeFlag (.word zero) (.word one_variant2))
    (.word one_variant2) [] :=
  Evaluates.wordNeFlag_ne (by decide) .word .word

example : Evaluates [] [] (Expr.wordLtFlag (.word zero) (.word one_variant2))
    (.word one_variant2) [] :=
  Evaluates.wordLtFlag_lt (definitions := [])
    (by decide) .word .word .word .word .nil .nil .nil

example : Evaluates [] [] (Expr.wordLeFlag (.word one_variant2) (.word zero))
    (.word zero) [] :=
  Evaluates.wordLeFlag_gt (by decide) .word .word

example : Evaluates [] [] (Expr.wordGeFlag (.word one_variant2) (.word zero))
    (.word one_variant2) [] :=
  Evaluates.wordGeFlag_not_lt (definitions := [])
    (by decide) .word .word .word .word .nil .nil .nil

private def boolProgram (body : Expr) : Program := {
  resultType := .bool
  body
}

private def testValuesTypesAndFuel : IO Unit := do
  let maximum := Word.maximum
  let cases : List (String × Program × Nat × Value) := [
    ("wordNeFlag false", wordProgram_variant
      (Expr.wordNeFlag (.word maximum) (.word maximum)), 10, .word zero),
    ("wordNeFlag true", wordProgram_variant
      (Expr.wordNeFlag (.word zero) (.word maximum)), 10, .word one_variant2),
    ("wordLtFlag true", wordProgram_variant
      (Expr.wordLtFlag (.word zero) (.word maximum)), 14, .word one_variant2),
    ("wordLtFlag false", wordProgram_variant
      (Expr.wordLtFlag (.word maximum) (.word zero)), 14, .word zero),
    ("wordLeFlag true", wordProgram_variant
      (Expr.wordLeFlag (.word zero) (.word maximum)), 10, .word one_variant2),
    ("wordLeFlag false", wordProgram_variant
      (Expr.wordLeFlag (.word maximum) (.word zero)), 10, .word zero),
    ("wordGeFlag true", wordProgram_variant
      (Expr.wordGeFlag (.word maximum) (.word zero)), 16, .word one_variant2),
    ("wordGeFlag false", wordProgram_variant
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
    assertTrue (!(wordProgram_variant body).check)
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

private def testFaultOrder_variant3 : IO Unit := do
  let rightWithEffect := allocatingWritingWord_variant zero one_variant2 zero
  let leftFaults : List (String × Program) := [
    ("wordNeFlag", wordProgram_variant (Expr.wordNeFlag (.var 99) rightWithEffect)),
    ("wordLtFlag", wordProgram_variant (Expr.wordLtFlag (.var 99) rightWithEffect)),
    ("wordLeFlag", wordProgram_variant (Expr.wordLeFlag (.var 99) rightWithEffect)),
    ("wordGeFlag", wordProgram_variant (Expr.wordGeFlag (.var 99) rightWithEffect))
  ]
  for (name, program) in leftFaults do
    match program.runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{name} evaluated its right operand after a left fault"
    | result =>
        throw (IO.userError s!"{name} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord_variant zero one_variant2 Word.maximum
  let rightFaults : List (String × Nat × Program) := [
    ("wordNeFlag", 100, wordProgram_variant (Expr.wordNeFlag leftWithEffect (.var 100))),
    ("wordLtFlag", 101, wordProgram_variant (Expr.wordLtFlag leftWithEffect (.var 100))),
    ("wordLeFlag", 100, wordProgram_variant (Expr.wordLeFlag leftWithEffect (.var 100))),
    ("wordGeFlag", 101, wordProgram_variant (Expr.wordGeFlag leftWithEffect (.var 100)))
  ]
  for (name, expectedIndex, program) in rightFaults do
    match program.runStateful 64 with
    | .fault (.unboundVariable actualIndex) state =>
        assertTrue (actualIndex == expectedIndex)
          s!"{name} exposed unbound index {actualIndex}, expected {expectedIndex}"
        assertTrue (state.store == [.word one_variant2])
          s!"{name} right fault did not observe the completed left store"
    | result =>
        throw (IO.userError s!"{name} exposed the wrong right fault: {reprStr result}")

private def testEffectsAndExactFuel_variant2 : IO Unit := do
  let two := Word.ofNatModulo 2
  let left := allocatingWritingWord_variant zero one_variant2 Word.maximum
  let right := allocatingWritingWord_variant zero two zero
  let cases : List (String × Program × Nat × Value) := [
    ("wordNeFlag", wordProgram_variant (Expr.wordNeFlag left right), 34, .word one_variant2),
    ("wordLtFlag", wordProgram_variant (Expr.wordLtFlag left right), 38, .word zero),
    ("wordLeFlag", wordProgram_variant (Expr.wordLeFlag left right), 34, .word zero),
    ("wordGeFlag", wordProgram_variant (Expr.wordGeFlag left right), 40, .word one_variant2)
  ]
  for (name, program, exactFuel, expected) in cases do
    assertTrue program.check s!"effectful {name} failed to type-check"
    assertTrue (program.run exactFuel.pred == .outOfFuel)
      s!"effectful {name} finished below its exact fuel boundary"
    assertTrue
      (program.runStateful exactFuel ==
        .done expected [.word one_variant2, .word two])
      s!"{name} did not evaluate and write left then right exactly once"

/-- Cover proof APIs, values, types, fuel, faults, and effect order. -/
def testCoreDerivedComparisonFlags : IO Unit := do
  testValuesTypesAndFuel
  testBooleanDistinction
  testFaultOrder_variant3
  testEffectsAndExactFuel_variant2

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreDerivedComparisons
/-! Semantic regressions for the derived boolean word comparisons. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def one_variant3 : Word := Word.ofNatModulo 1

example : HasType [] (Expr.wordNe (.word zero) (.word one_variant3)) .bool :=
  HasType.wordNe .word .word

example : HasType [] (Expr.wordLt (.word zero) (.word one_variant3)) .bool :=
  HasType.wordLt .word .word

example : HasType [] (Expr.wordLe (.word zero) (.word one_variant3)) .bool :=
  HasType.wordLe .word .word

example : HasType [] (Expr.wordGe (.word zero) (.word one_variant3)) .bool :=
  HasType.wordGe .word .word

example : infer? [] (Expr.wordNe (.word zero) (.word one_variant3)) = some .bool :=
  infer_wordNe rfl rfl

example : infer? [] (Expr.wordLt (.word zero) (.word one_variant3)) = some .bool :=
  infer_wordLt rfl rfl

example : infer? [] (Expr.wordLe (.word zero) (.word one_variant3)) = some .bool :=
  infer_wordLe rfl rfl

example : infer? [] (Expr.wordGe (.word zero) (.word one_variant3)) = some .bool :=
  infer_wordGe rfl rfl

example : Evaluates [] [] (Expr.wordNe (.word zero) (.word one_variant3)) (.bool true) [] :=
  Evaluates.wordNe_ne (by decide) .word .word

example : Evaluates [] [] (Expr.wordLe (.word zero) (.word one_variant3)) (.bool true) [] :=
  Evaluates.wordLe_not_gt (by decide) .word .word

example : Evaluates [] [] (Expr.wordLt (.word zero) (.word one_variant3)) (.bool true) [] :=
  Evaluates.wordLt_lt (definitions := [])
    (by decide) .word .word .word .word .nil .nil .nil

example : Evaluates [] [] (Expr.wordGe (.word one_variant3) (.word zero)) (.bool true) [] :=
  Evaluates.wordGe_not_lt (definitions := [])
    (by decide) .word .word .word .word .nil .nil .nil

private def booleanProgram (body : Expr) : Program := {
  resultType := .bool
  body
}

private def testValuesTypesAndFuel_variant : IO Unit := do
  let zero := Word.zero
  let maximum := Word.maximum
  let cases : List (String × Program × Nat × Value) := [
    ("wordNe false", booleanProgram
      (Expr.wordNe (.word maximum) (.word maximum)), 7, .bool false),
    ("wordNe true", booleanProgram
      (Expr.wordNe (.word zero) (.word maximum)), 7, .bool true),
    ("wordLt true", booleanProgram
      (Expr.wordLt (.word zero) (.word maximum)), 11, .bool true),
    ("wordLt false", booleanProgram
      (Expr.wordLt (.word maximum) (.word zero)), 11, .bool false),
    ("wordLe true", booleanProgram
      (Expr.wordLe (.word zero) (.word maximum)), 7, .bool true),
    ("wordLe false", booleanProgram
      (Expr.wordLe (.word maximum) (.word zero)), 7, .bool false),
    ("wordGe true", booleanProgram
      (Expr.wordGe (.word maximum) (.word zero)), 13, .bool true),
    ("wordGe false", booleanProgram
      (Expr.wordGe (.word zero) (.word maximum)), 13, .bool false)
  ]
  for (name, program, exactFuel, expected) in cases do
    assertTrue program.check s!"{name} failed to type-check"
    assertTrue (program.run (exactFuel - 1) == .outOfFuel)
      s!"{name} finished below its exact fuel boundary"
    assertTrue (program.run exactFuel == .done expected)
      s!"{name} failed at its exact fuel boundary"

  for body in [
      Expr.wordNe .unit (.word zero), Expr.wordLt .unit (.word zero),
      Expr.wordLe (.word zero) .unit, Expr.wordGe (.word zero) .unit
    ] do
    let program : Program := { resultType := .bool, body }
    assertTrue (!program.check)
      s!"derived comparison accepted a non-word operand: {reprStr body}"

private def testLeftFirstFaults : IO Unit := do
  let one := Word.ofNatModulo 1
  let rightWithEffect := allocatingWritingWord_variant Word.zero one Word.zero
  let neFault : Program := {
    resultType := .bool
    body := Expr.wordNe (.var 99) rightWithEffect
  }
  match neFault.runStateful 2 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordNe evaluated its right operand after a left fault"
  | result =>
      throw (IO.userError s!"wordNe exposed the wrong fault: {reprStr result}")

  let leFault : Program := {
    resultType := .bool
    body := Expr.wordLe (.var 99) rightWithEffect
  }
  match leFault.runStateful 2 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordLe evaluated its right operand after a left fault"
  | result =>
      throw (IO.userError s!"wordLe exposed the wrong fault: {reprStr result}")

  let ltFault : Program := {
    resultType := .bool
    body := Expr.wordLt (.var 99) rightWithEffect
  }
  match ltFault.runStateful 2 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordLt evaluated its right operand after a left fault"
  | result =>
      throw (IO.userError s!"wordLt exposed the wrong fault: {reprStr result}")

  let geFault : Program := {
    resultType := .bool
    body := Expr.wordGe (.var 99) rightWithEffect
  }
  match geFault.runStateful 3 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordGe evaluated its right operand after a left fault"
  | result =>
      throw (IO.userError s!"wordGe exposed the wrong fault: {reprStr result}")

private def testEffectOrder : IO Unit := do
  let one := Word.ofNatModulo 1
  let two := Word.ofNatModulo 2
  let left := allocatingWritingWord_variant Word.zero one Word.maximum
  let right := allocatingWritingWord_variant Word.zero two Word.zero
  let ne : Program := {
    resultType := .bool
    body := Expr.wordNe left right
  }
  let le : Program := {
    resultType := .bool
    body := Expr.wordLe left right
  }
  let lt : Program := {
    resultType := .bool
    body := Expr.wordLt left right
  }
  let ge : Program := {
    resultType := .bool
    body := Expr.wordGe left right
  }
  for (name, program) in [("wordNe", ne), ("wordLe", le),
      ("wordLt", lt), ("wordGe", ge)] do
    assertTrue program.check s!"effectful {name} failed to type-check"
  assertTrue
    (ne.runStateful 31 ==
      .done (.bool true) [.word one, .word two])
    "wordNe must evaluate and write left then right exactly once"
  assertTrue
    (le.runStateful 31 ==
      .done (.bool false) [.word one, .word two])
    "wordLe must evaluate and write left then right exactly once"
  assertTrue
    (lt.runStateful 35 ==
      .done (.bool false) [.word one, .word two])
    "wordLt must evaluate and write left then right exactly once"
  assertTrue
    (ge.runStateful 37 ==
      .done (.bool true) [.word one, .word two])
    "wordGe must evaluate and write left then right exactly once"

/-- Cover values, types, theorem interfaces, faults, effects, and exact fuel. -/
def testCoreDerivedComparisons : IO Unit := do
  testValuesTypesAndFuel_variant
  testLeftFirstFaults
  testEffectOrder

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreDerivedRenamingLaws
/-! Focused regressions for arbitrary renaming of older derived builders. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

/-- A genuinely non-insertion renaming: the first two free variables swap. -/
private def swap01 : Renaming
  | 0 => 1
  | 1 => 0
  | index + 2 => index + 2

example (value : Expr) :
    value.boolToWord.rename swap01 = (value.rename swap01).boolToWord :=
  Expr.rename_boolToWord value swap01

example (value : Expr) :
    value.wordToBool.rename swap01 = (value.rename swap01).wordToBool :=
  Expr.rename_wordToBool value swap01

example (value : Expr) :
    value.wordIsZero.rename swap01 = (value.rename swap01).wordIsZero :=
  Expr.rename_wordIsZero value swap01

example (value : Expr) :
    value.wordIsNonzero.rename swap01 = (value.rename swap01).wordIsNonzero :=
  Expr.rename_wordIsNonzero value swap01

example (left right : Expr) :
    (left.boolAnd right).rename swap01 =
      (left.rename swap01).boolAnd (right.rename swap01) :=
  Expr.rename_boolAnd left right swap01

example (left right : Expr) :
    (left.boolOr right).rename swap01 =
      (left.rename swap01).boolOr (right.rename swap01) :=
  Expr.rename_boolOr left right swap01

example (left right : Expr) :
    (left.wordEqFlag right).rename swap01 =
      (left.rename swap01).wordEqFlag (right.rename swap01) :=
  Expr.rename_wordEqFlag left right swap01

example (left right : Expr) :
    (left.wordGtFlag right).rename swap01 =
      (left.rename swap01).wordGtFlag (right.rename swap01) :=
  Expr.rename_wordGtFlag left right swap01

private def testGoldenRenamings : IO Unit := do
  let left : Expr := .var 0
  let right : Expr := .var 1
  let zero : Expr := .word Word.zero
  let one : Expr := .word (Word.ofNatModulo 1)

  assertTrue
    (left.boolToWord.rename swap01 == .ifE (.var 1) one zero)
    "boolToWord did not rename its free operand"
  assertTrue
    (left.wordToBool.rename swap01 ==
      Expr.unary .boolNot (Expr.binary .wordEq (.var 1) zero))
    "wordToBool did not rename its free operand"
  assertTrue
    (left.wordIsZero.rename swap01 ==
      (Expr.binary .wordEq (.var 1) zero).boolToWord)
    "wordIsZero did not rename its free operand"
  assertTrue
    (left.wordIsNonzero.rename swap01 == (Expr.var 1).wordIsNonzero)
    "wordIsNonzero did not rename its free operand"

  assertTrue
    ((left.boolAnd right).rename swap01 ==
      .ifE (.var 1) (.var 0) (.bool false))
    "boolAnd did not preserve condition and selected-branch positions"
  assertTrue
    ((left.boolOr right).rename swap01 ==
      .ifE (.var 1) (.bool true) (.var 0))
    "boolOr did not preserve condition and selected-branch positions"
  assertTrue
    ((left.wordEqFlag right).rename swap01 ==
      (Expr.binary .wordEq (.var 1) (.var 0)).boolToWord)
    "wordEqFlag did not rename both operands"
  assertTrue
    ((left.wordGtFlag right).rename swap01 ==
      (Expr.binary .wordGt (.var 1) (.var 0)).boolToWord)
    "wordGtFlag did not rename both operands"

private def runIn (expression : Expr) (environment : Environment) : RunResult :=
  Solcore.Core.run 32 (State.initial expression environment)

private def testRenamedEvaluation : IO Unit := do
  let one := Word.ofNatModulo 1
  let maximum := Word.maximum

  let conversion := (Expr.var 0).boolToWord.rename swap01
  assertTrue
    (runIn conversion [.word Word.zero, .bool true] == .done (.word one))
    "renamed conversion read the wrong environment position"

  let conjunction := (Expr.boolAnd (.var 0) (.var 1)).rename swap01
  assertTrue
    (runIn conjunction [.bool false, .bool true] == .done (.bool false))
    "renamed short-circuit expression changed its branch meaning"

  let comparison := (Expr.wordGtFlag (.var 0) (.var 1)).rename swap01
  assertTrue
    (runIn comparison [.word Word.zero, .word maximum] == .done (.word one))
    "renamed comparison flag read its operands in the wrong positions"

/-- Cover all eight public laws with a non-insertion mapping and representative
evaluation from each derived-builder family. -/
def testCoreDerivedRenamingLaws : IO Unit := do
  testGoldenRenamings
  testRenamedEvaluation

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreDerivedSignedComparison
/-! Focused proof and runtime regressions for effect-safe derived signed less-than. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

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
    .word .word .word .word .nil .nil .nil
example : Evaluates [] [] (Expr.wordSlt (.word zero) (.word one))
    (.bool true) [] :=
  Evaluates.wordSlt_both_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] [] (Expr.wordSlt (.word highBit) (.word Word.maximum))
    (.bool true) [] :=
  Evaluates.wordSlt_both_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] [] (Expr.wordSlt (.word zero) (.word Word.maximum))
    (.bool false) [] :=
  Evaluates.wordSlt_nonnegative_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] [] (Expr.wordSlt (.word Word.maximum) (.word zero))
    (.bool true) [] :=
  Evaluates.wordSlt_negative_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil

private def testValuesTypesAndFuel_variant2 : IO Unit := do
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

private def testFaultOrder_variant4 : IO Unit := do
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

private def testEffectOrder_variant : IO Unit := do
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
  testValuesTypesAndFuel_variant2
  testFaultOrder_variant4
  testEffectOrder_variant

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreDerivedSignedNonStrictComparisonFlags
/-! Regressions for word-valued signed less/greater-than-or-equal builders. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def positiveMaximum_variant : Word := word (2 ^ 255 - 1)

example : Expr.wordSleFlag (.word zero) (.word one) =
    (Expr.wordSle (.word zero) (.word one)).boolToWord :=
  Expr.wordSleFlag_expansion (.word zero) (.word one)
example : Expr.wordSgeFlag (.word one) (.word zero) =
    (Expr.wordSge (.word one) (.word zero)).boolToWord :=
  Expr.wordSgeFlag_expansion (.word one) (.word zero)
example : HasType [] (Expr.wordSleFlag (.word zero) (.word one)) .word :=
  HasType.wordSleFlag .word .word
example : HasType [] (Expr.wordSgeFlag (.word one) (.word zero)) .word :=
  HasType.wordSgeFlag .word .word
example : infer? [] (Expr.wordSleFlag (.word zero) (.word one)) = some .word :=
  infer_wordSleFlag rfl rfl
example : infer? [] (Expr.wordSgeFlag (.word one) (.word zero)) = some .word :=
  infer_wordSgeFlag rfl rfl
example (left right : Expr) (mapping : Renaming) :
    (left.wordSleFlag right).rename mapping =
      (left.rename mapping).wordSleFlag (right.rename mapping) :=
  Expr.rename_wordSleFlag left right mapping
example (left right : Expr) (mapping : Renaming) :
    (left.wordSgeFlag right).rename mapping =
      (left.rename mapping).wordSgeFlag (right.rename mapping) :=
  Expr.rename_wordSgeFlag left right mapping
example (left right : Expr) (cutoff : Nat) :
    (left.wordSleFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSleFlag (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSleFlag left right cutoff
example (left right : Expr) (cutoff : Nat) :
    (left.wordSgeFlag right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSgeFlag (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSgeFlag left right cutoff

example : Evaluates [] [] (Expr.wordSleFlag (.word zero) (.word one))
    (.word (if !zero.signedGt one then one else zero)) [] :=
  Evaluates.wordSleFlag .word .word
example : Evaluates [] [] (Expr.wordSleFlag (.word zero) (.word one))
    (.word one) [] :=
  Evaluates.wordSleFlag_both_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSleFlag (.word highBit) (.word Word.maximum)) (.word one) [] :=
  Evaluates.wordSleFlag_both_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSleFlag (.word zero) (.word Word.maximum)) (.word zero) [] :=
  Evaluates.wordSleFlag_nonnegative_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSleFlag (.word Word.maximum) (.word zero)) (.word one) [] :=
  Evaluates.wordSleFlag_negative_nonnegative (by decide) (by decide) .word .word

example : Evaluates [] [] (Expr.wordSgeFlag (.word one) (.word zero))
    (.word (if !zero.signedGt one then one else zero)) [] :=
  Evaluates.wordSgeFlag (definitions := []) .word .word .word .word .nil .nil .nil
example : Evaluates [] [] (Expr.wordSgeFlag (.word one) (.word zero))
    (.word one) [] :=
  Evaluates.wordSgeFlag_both_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSgeFlag (.word Word.maximum) (.word highBit)) (.word one) [] :=
  Evaluates.wordSgeFlag_both_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSgeFlag (.word zero) (.word Word.maximum)) (.word one) [] :=
  Evaluates.wordSgeFlag_nonnegative_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSgeFlag (.word Word.maximum) (.word zero)) (.word zero) [] :=
  Evaluates.wordSgeFlag_negative_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil

private def wordProgram_variant2 (body : Expr) : Program := { resultType := .word, body }

private def testValuesTypesAndFuel_variant3 : IO Unit := do
  let cases : List (String × Word × Word × Word × Word) := [
    ("zero one", zero, one, one, zero),
    ("one zero", one, zero, zero, one),
    ("positive max zero", positiveMaximum_variant, zero, zero, one),
    ("zero positive max", zero, positiveMaximum_variant, one, zero),
    ("maximum high bit", Word.maximum, highBit, zero, one),
    ("high bit maximum", highBit, Word.maximum, one, zero),
    ("zero maximum", zero, Word.maximum, zero, one),
    ("maximum zero", Word.maximum, zero, one, zero),
    ("zero equal", zero, zero, one, one),
    ("positive equal", positiveMaximum_variant, positiveMaximum_variant, one, one),
    ("negative equal", Word.maximum, Word.maximum, one, one)
  ]
  for (name, left, right, sleExpected, sgeExpected) in cases do
    let sle := wordProgram_variant2 (Expr.wordSleFlag (.word left) (.word right))
    let sge := wordProgram_variant2 (Expr.wordSgeFlag (.word left) (.word right))
    assertTrue (sle.check && sge.check) s!"{name} failed to type-check"
    assertTrue (sle.run 9 == .outOfFuel &&
      sle.run 10 == .done (.word sleExpected)) s!"SleFlag {name} fuel/value"
    assertTrue (sge.run 15 == .outOfFuel &&
      sge.run 16 == .done (.word sgeExpected)) s!"SgeFlag {name} fuel/value"

  for body in [Expr.wordSleFlag .unit (.word zero),
      Expr.wordSleFlag (.word one) .unit, Expr.wordSgeFlag .unit (.word zero),
      Expr.wordSgeFlag (.word one) .unit] do
    assertTrue (!(wordProgram_variant2 body).check) "flag accepted nonword operand"
  for body in [Expr.wordSleFlag (.word zero) (.word one),
      Expr.wordSgeFlag (.word one) (.word zero)] do
    let wrong : Program := { resultType := .bool, body }
    assertTrue (!wrong.check) "word-valued flag accepted bool result"

  assertTrue ((wordProgram_variant2 (Expr.wordSleFlag .unit (.word one))).run 10 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "SleFlag source-left payload was not direct"
  assertTrue ((wordProgram_variant2 (Expr.wordSleFlag (.word one) .unit)).run 10 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "SleFlag source-right payload was not direct"
  assertTrue ((wordProgram_variant2 (Expr.wordSgeFlag .unit (.word one))).run 16 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "SgeFlag source-left payload was not swapped"
  assertTrue ((wordProgram_variant2 (Expr.wordSgeFlag (.word one) .unit)).run 16 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "SgeFlag source-right payload was not swapped"

private def testFaultOrder_variant5 : IO Unit := do
  let rightEffect := allocatingWritingWord zero one Word.maximum
  for (name, body) in [("sle", Expr.wordSleFlag (.var 99) rightEffect),
      ("sge", Expr.wordSgeFlag (.var 99) rightEffect)] do
    match (wordProgram_variant2 body).runStateful 12 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty s!"{name} evaluated right after left fault"
    | result => throw (IO.userError s!"{name} wrong left fault: {reprStr result}")

  let leftEffect := allocatingWritingWord zero one Word.maximum
  match (wordProgram_variant2 (Expr.wordSleFlag leftEffect (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one]) "SleFlag lost left store"
  | result => throw (IO.userError s!"SleFlag wrong right fault: {reprStr result}")
  match (wordProgram_variant2 (Expr.wordSgeFlag leftEffect (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 101) state =>
      assertTrue (state.store == [.word one]) "SgeFlag lost left store"
  | result => throw (IO.userError s!"SgeFlag wrong weakened fault: {reprStr result}")

private def testEffects : IO Unit := do
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero (word 2) zero
  let sle := wordProgram_variant2 (Expr.wordSleFlag left right)
  let sge := wordProgram_variant2 (Expr.wordSgeFlag left right)
  assertTrue (sle.run 33 == .outOfFuel &&
    sle.runStateful 34 == .done (.word one) [.word one, .word (word 2)])
    "SleFlag missed exact effect/store boundary"
  assertTrue (sge.run 39 == .outOfFuel &&
    sge.runStateful 40 == .done (.word zero) [.word one, .word (word 2)])
    "SgeFlag missed exact effect/store boundary"

/-- Cover twenty APIs plus canonical values, types, faults, effects, and fuel. -/
def testCoreDerivedSignedNonStrictComparisonFlags : IO Unit := do
  testValuesTypesAndFuel_variant3
  testFaultOrder_variant5
  testEffects

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreDerivedSignedNonStrictComparisons
/-! Focused regressions for derived signed less/greater-than-or-equal. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def positiveMaximum_variant2 : Word := word (2 ^ 255 - 1)

example : Expr.wordSle (.word zero) (.word one) =
    .unary .boolNot (.binary .wordSgt (.word zero) (.word one)) :=
  Expr.wordSle_expansion (.word zero) (.word one)
example : Expr.wordSge (.word one) (.word zero) =
    .unary .boolNot (Expr.wordSlt (.word one) (.word zero)) :=
  Expr.wordSge_expansion (.word one) (.word zero)
example : HasType [] (Expr.wordSle (.word zero) (.word one)) .bool :=
  HasType.wordSle .word .word
example : HasType [] (Expr.wordSge (.word one) (.word zero)) .bool :=
  HasType.wordSge .word .word
example : infer? [] (Expr.wordSle (.word zero) (.word one)) = some .bool :=
  infer_wordSle rfl rfl
example : infer? [] (Expr.wordSge (.word one) (.word zero)) = some .bool :=
  infer_wordSge rfl rfl
example (left right : Expr) (mapping : Renaming) :
    (left.wordSle right).rename mapping =
      (left.rename mapping).wordSle (right.rename mapping) :=
  Expr.rename_wordSle left right mapping
example (left right : Expr) (mapping : Renaming) :
    (left.wordSge right).rename mapping =
      (left.rename mapping).wordSge (right.rename mapping) :=
  Expr.rename_wordSge left right mapping
example (left right : Expr) (cutoff : Nat) :
    (left.wordSle right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSle (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSle left right cutoff
example (left right : Expr) (cutoff : Nat) :
    (left.wordSge right).weakenAt cutoff =
      (left.weakenAt cutoff).wordSge (right.weakenAt cutoff) :=
  Expr.weakenAt_wordSge left right cutoff

example : Evaluates [] [] (Expr.wordSle (.word zero) (.word one))
    (.bool (!zero.signedGt one)) [] :=
  Evaluates.wordSle .word .word
example : Evaluates [] [] (Expr.wordSle (.word zero) (.word one)) (.bool true) [] :=
  Evaluates.wordSle_both_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSle (.word highBit) (.word Word.maximum)) (.bool true) [] :=
  Evaluates.wordSle_both_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSle (.word zero) (.word Word.maximum)) (.bool false) [] :=
  Evaluates.wordSle_nonnegative_negative (by decide) (by decide) .word .word
example : Evaluates [] []
    (Expr.wordSle (.word Word.maximum) (.word zero)) (.bool true) [] :=
  Evaluates.wordSle_negative_nonnegative (by decide) (by decide) .word .word

example : Evaluates [] [] (Expr.wordSge (.word one) (.word zero))
    (.bool (!zero.signedGt one)) [] :=
  Evaluates.wordSge (definitions := []) .word .word .word .word .nil .nil .nil
example : Evaluates [] [] (Expr.wordSge (.word one) (.word zero)) (.bool true) [] :=
  Evaluates.wordSge_both_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSge (.word Word.maximum) (.word highBit)) (.bool true) [] :=
  Evaluates.wordSge_both_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSge (.word zero) (.word Word.maximum)) (.bool true) [] :=
  Evaluates.wordSge_nonnegative_negative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil
example : Evaluates [] []
    (Expr.wordSge (.word Word.maximum) (.word zero)) (.bool false) [] :=
  Evaluates.wordSge_negative_nonnegative (definitions := [])
    (by decide) (by decide) .word .word .word .word .nil .nil .nil

private def boolProgram_variant (body : Expr) : Program := { resultType := .bool, body }

private def testValuesTypesAndFuel_variant4 : IO Unit := do
  let cases : List (String × Word × Word × Bool × Bool) := [
    ("zero one", zero, one, true, false),
    ("one zero", one, zero, false, true),
    ("positive maximum zero", positiveMaximum_variant2, zero, false, true),
    ("zero positive maximum", zero, positiveMaximum_variant2, true, false),
    ("maximum high bit", Word.maximum, highBit, false, true),
    ("high bit maximum", highBit, Word.maximum, true, false),
    ("zero maximum", zero, Word.maximum, false, true),
    ("maximum zero", Word.maximum, zero, true, false),
    ("maximum equal", Word.maximum, Word.maximum, true, true)
  ]
  for (name, left, right, sleExpected, sgeExpected) in cases do
    let sle := boolProgram_variant (Expr.wordSle (.word left) (.word right))
    let sge := boolProgram_variant (Expr.wordSge (.word left) (.word right))
    assertTrue (sle.check && sge.check) s!"non-strict {name} failed to type-check"
    assertTrue (sle.run 6 == .outOfFuel && sle.run 7 == .done (.bool sleExpected))
      s!"wordSle {name} missed exact 6/7 fuel"
    assertTrue (sge.run 12 == .outOfFuel && sge.run 13 == .done (.bool sgeExpected))
      s!"wordSge {name} missed exact 12/13 fuel"

  for body in [Expr.wordSle .unit (.word zero), Expr.wordSle (.word one) .unit,
      Expr.wordSge .unit (.word zero), Expr.wordSge (.word one) .unit] do
    assertTrue (!(boolProgram_variant body).check) "non-strict comparison accepted bad operand"
  let wrongSle : Program := {
    resultType := .word
    body := Expr.wordSle (.word zero) (.word one)
  }
  let wrongSge : Program := {
    resultType := .word
    body := Expr.wordSge (.word one) (.word zero)
  }
  assertTrue (!wrongSle.check && !wrongSge.check) "non-strict accepted word result"

  assertTrue ((boolProgram_variant (Expr.wordSle .unit (.word one))).run 7 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "wordSle source-left payload was not direct"
  assertTrue ((boolProgram_variant (Expr.wordSle (.word one) .unit)).run 7 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSle source-right payload was not direct"
  assertTrue ((boolProgram_variant (Expr.wordSge .unit (.word one))).run 13 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSge source-left payload was not swapped"
  assertTrue ((boolProgram_variant (Expr.wordSge (.word one) .unit)).run 13 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "wordSge source-right payload was not swapped"

private def testFaultOrder_variant6 : IO Unit := do
  let effectfulRight := allocatingWritingWord zero one Word.maximum
  for (name, body) in [("sle", Expr.wordSle (.var 99) effectfulRight),
      ("sge", Expr.wordSge (.var 99) effectfulRight)] do
    match (boolProgram_variant body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty s!"{name} evaluated right after left fault"
    | result => throw (IO.userError s!"{name} wrong left fault: {reprStr result}")

  let effectfulLeft := allocatingWritingWord zero one Word.maximum
  match (boolProgram_variant (Expr.wordSle effectfulLeft (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one]) "sle right fault lost left store"
  | result => throw (IO.userError s!"sle wrong right fault: {reprStr result}")
  match (boolProgram_variant (Expr.wordSge effectfulLeft (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 101) state =>
      assertTrue (state.store == [.word one]) "sge right fault lost left store"
  | result => throw (IO.userError s!"sge wrong weakened fault: {reprStr result}")

private def testEffects_variant : IO Unit := do
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero (word 2) zero
  let sle := boolProgram_variant (Expr.wordSle left right)
  let sge := boolProgram_variant (Expr.wordSge left right)
  assertTrue (sle.run 30 == .outOfFuel &&
    sle.runStateful 31 == .done (.bool true) [.word one, .word (word 2)])
    "wordSle missed exact effect/store boundary"
  assertTrue (sge.run 36 == .outOfFuel &&
    sge.runStateful 37 == .done (.bool false) [.word one, .word (word 2)])
    "wordSge missed exact effect/store boundary"

/-- Cover all twenty theorems plus truth tables, types, faults, effects, and fuel. -/
def testCoreDerivedSignedNonStrictComparisons : IO Unit := do
  testValuesTypesAndFuel_variant4
  testFaultOrder_variant6
  testEffects_variant

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreDirectWordComparisons
/-! Focused proof and runtime regressions for direct boolean word comparisons. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def two_variant2 : Word := Word.ofNatModulo 2

example : BinaryOp.wordEq.apply (.word one_variant) (.word two_variant2) =
    some (.bool (one_variant == two_variant2)) :=
  BinaryOp.apply_wordEq one_variant two_variant2
example : BinaryOp.wordGt.apply (.word two_variant2) (.word one_variant) =
    some (.bool (decide (two_variant2 > one_variant))) :=
  BinaryOp.apply_wordGt two_variant2 one_variant

example : Evaluates [] [] (.binary .wordEq (.word one_variant) (.word two_variant2))
    (.bool (one_variant == two_variant2)) [] :=
  Evaluates.wordEq .word .word
example : Evaluates [] [] (.binary .wordEq (.word one_variant) (.word one_variant))
    (.bool true) [] :=
  Evaluates.wordEq_eq rfl .word .word
example : Evaluates [] [] (.binary .wordEq (.word one_variant) (.word two_variant2))
    (.bool false) [] :=
  Evaluates.wordEq_ne (by decide) .word .word
example : Evaluates [] [] (.binary .wordGt (.word two_variant2) (.word one_variant))
    (.bool (decide (two_variant2 > one_variant))) [] :=
  Evaluates.wordGt .word .word
example : Evaluates [] [] (.binary .wordGt (.word two_variant2) (.word one_variant))
    (.bool true) [] :=
  Evaluates.wordGt_gt (by decide) .word .word
example : Evaluates [] [] (.binary .wordGt (.word one_variant) (.word two_variant2))
    (.bool false) [] :=
  Evaluates.wordGt_not_gt (by decide) .word .word

private def testValuesTypesAndLiteralFuel_variant4 : IO Unit := do
  let cases : List (String × BinaryOp × Word × Word × Bool) := [
    ("zero eq zero", .wordEq, zero, zero, true),
    ("maximum eq maximum", .wordEq, Word.maximum, Word.maximum, true),
    ("zero eq maximum", .wordEq, zero, Word.maximum, false),
    ("one eq two", .wordEq, one_variant, two_variant2, false),
    ("maximum gt zero", .wordGt, Word.maximum, zero, true),
    ("two gt one", .wordGt, two_variant2, one_variant, true),
    ("zero gt maximum", .wordGt, zero, Word.maximum, false),
    ("maximum gt maximum", .wordGt, Word.maximum, Word.maximum, false),
    ("one gt two", .wordGt, one_variant, two_variant2, false)
  ]
  for (name, op, left, right, expected) in cases do
    let witness := boolProgram (.binary op (.word left) (.word right))
    assertTrue witness.check s!"{name} failed to type-check as bool"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done (.bool expected))
      s!"{name} failed at the literal binary fuel boundary"

  for op in [BinaryOp.wordEq, .wordGt] do
    for body in [
        Expr.binary op .unit (.word one_variant),
        Expr.binary op (.word one_variant) .unit
      ] do
      assertTrue (!(boolProgram body).check)
        s!"{reprStr op} accepted a non-word operand: {reprStr body}"

    let body := Expr.binary op (.word two_variant2) (.word one_variant)
    let wrongResult : Program := { resultType := .word, body }
    assertTrue (!wrongResult.check)
      s!"{reprStr op} was accepted with a word result"

    assertTrue
      ((boolProgram (.binary op .unit (.word one_variant))).run 5 ==
        .fault (.invalidBinaryOperands op .unit (.word one_variant)))
      s!"raw {reprStr op} did not expose its invalid left operand"
    assertTrue
      ((boolProgram (.binary op (.word one_variant) .unit)).run 5 ==
        .fault (.invalidBinaryOperands op (.word one_variant) .unit))
      s!"raw {reprStr op} did not expose its invalid right operand"

private def testFaultOrder_variant7 : IO Unit := do
  let rightWithEffect := allocatingWritingWord_variant zero one_variant zero
  for op in [BinaryOp.wordEq, .wordGt] do
    let body := Expr.binary op (.var 99) rightWithEffect
    match (boolProgram body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated its right operand after a left fault"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord_variant zero one_variant Word.maximum
  for op in [BinaryOp.wordEq, .wordGt] do
    let body := Expr.binary op leftWithEffect (.var 100)
    match (boolProgram body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one_variant])
          s!"{reprStr op} right fault did not observe the left store"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands_variant3 : IO Unit := do
  let left := allocatingWritingWord_variant zero one_variant Word.maximum
  let right := allocatingWritingWord_variant zero two_variant2 zero
  for (name, op, expected) in [
      ("wordEq", BinaryOp.wordEq, false),
      ("wordGt", BinaryOp.wordGt, true)
    ] do
    let witness := boolProgram (.binary op left right)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.bool expected) [.word one_variant, .word two_variant2])
      s!"{name} did not evaluate left then right exactly once"

/-- Cover all eight theorems plus values, order, faults, effects, and fuel. -/
def testCoreDirectWordComparisons : IO Unit := do
  testValuesTypesAndLiteralFuel_variant4
  testFaultOrder_variant7
  testEffectfulOperands_variant3

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreIntegers
/-! Native Integer cases cover mathematical range, signs, primitive typing,
shared cells, genuine checkpoints, and the existing Word-only host boundary. -/

set_option autoImplicit false

namespace Tests.CoreIntegers

open Solcore.Core

private def huge : Int := Int.ofNat (2 ^ 300)

private def arithmetic (op : BinaryOp) (left right : Int) : Program := {
  resultType := op.resultType
  body := .binary op (.integer left) (.integer right)
}

private def unary (op : UnaryOp) (value : Expr) : Program := {
  resultType := op.resultType
  body := .unary op value
}

example (left right : Int) : Evaluates [] []
    (.binary .integerDiv (.integer left) (.integer right))
    (.integer (Integer.divide left right)) [] :=
  .binary .integer .integer rfl

example (left right : Int) : Evaluates [] []
    (.binary .integerMod (.integer left) (.integer right))
    (.integer (Integer.modulo left right)) [] :=
  .binary .integer .integer rfl

example (value : Int) : Evaluates [] []
    (.unary .integerToWord (.integer value)) (.word (Word.ofIntModulo value)) [] :=
  .unary .integer rfl

private def effects : Program := {
  resultType := .integer
  body := .letE (.newCell .integer (.integer 1))
    (.binary .integerSub
      (.letE (.storeCell (.var 0) (.integer 7)) (.loadCell (.var 1)))
      (.letE (.storeCell (.var 0) (.integer 10)) (.loadCell (.var 1))))
}

private theorem effects_checked : effects.check = true := rfl
private theorem effects_run : effects.runStateful 64 = .done (.integer (-3)) [.integer 10] := rfl

/-- The executable CEK trace supplies a genuine finite evaluation witness. -/
example : Evaluates [] [] effects.body (.integer (-3)) [.integer 10] :=
  runStateful_evaluation_sound effects_run

example (fuel : Nat) : (effects.runStateful fuel).HasType .integer :=
  effects.checked_runStateful_has_type effects_checked fuel

example (fuel additional : Nat) (checkpoint : State)
    (suspended : effects.runStateful fuel = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType .integer ∧
      runStateful additional checkpoint = effects.runStateful (fuel + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound effects_checked).bodyHasType)
    suspended additional

private def capture : Program := {
  resultType := .integer
  body := .letE (.newCell .integer (.integer 4))
    (.letE (.lambda .integer .integer
      (.letE (.storeCell (.var 1) (.binary .integerAdd (.loadCell (.var 1)) (.var 0)))
        (.loadCell (.var 2))))
      (.letE (.apply (.var 0) (.integer 3)) (.apply (.var 1) (.integer 5))))
}

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def assertProgram (program : Program) (value : Value) (store : Store := []) : IO Unit := do
  assertTrue program.check "native Integer program did not type-check"
  assertTrue (program.runStateful 1000 == .done value store)
    s!"native Integer runner returned {reprStr (program.runStateful 1000)}"

def run : IO Unit := do
  assertProgram { resultType := .integer, body := .integer (-huge) } (.integer (-huge))
  assertProgram (arithmetic .integerAdd huge huge) (.integer (2 * huge))
  assertProgram (arithmetic .integerSub (-huge) 17) (.integer (-huge - 17))
  assertProgram (arithmetic .integerMul huge (-huge)) (.integer (-(huge * huge)))
  for left in [-huge - 7, -7, 0, 7, huge + 7] do
    for right in [-3, -1, 0, 1, 3] do
      assertProgram (arithmetic .integerDiv left right)
        (.integer (if right = 0 then 0 else left / right))
      assertProgram (arithmetic .integerMod left right)
        (.integer (if right = 0 then 0 else left % right))
      assertProgram (arithmetic .integerEq left right) (.bool (left == right))
      assertProgram (arithmetic .integerLt left right) (.bool (decide (left < right)))
      assertProgram (arithmetic .integerAnd left right) (.integer (Integer.bitAnd left right))
      assertProgram (arithmetic .integerOr left right) (.integer (Integer.bitOr left right))
      assertProgram (arithmetic .integerXor left right) (.integer (Integer.bitXor left right))
    assertProgram (unary .integerNot (.integer left)) (.integer (~~~left))
    assertProgram (unary .integerToWord (.integer left)) (.word (Word.ofIntModulo left))
  assertProgram (arithmetic .integerAnd (-1) huge) (.integer huge)
  assertProgram (arithmetic .integerOr (-1) huge) (.integer (-1))
  assertProgram (arithmetic .integerXor (-1) huge) (.integer (~~~huge))
  let maxWord := Word.ofNatModulo (wordModulus - 1)
  assertProgram (unary .wordToInteger (.word maxWord)) (.integer (Int.ofNat maxWord.val))

  assertProgram effects (.integer (-3)) [.integer 10]
  assertProgram capture (.integer 12) [.integer 12]
  assertTrue (effects.runHostStateful 100 == .done (.integer (-3)) [.integer 10])
    "native Integer pure execution must have the same host-runner outcome"
  match effects.runStateful 6 with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 100 checkpoint == effects.runStateful 106)
        "Integer cell effects must resume from the genuine checkpoint"
  | other => throw (IO.userError s!"expected Integer suspension, got {reprStr other}")

  let bad : Program := {
    resultType := .integer
    body := .binary .integerAdd (.integer 1) (.word Word.zero) }
  assertTrue (!bad.check) "integer primitives must reject Word operands"
  assertTrue (!(unary .wordToInteger (.integer 1)).check)
    "wordToInteger must require a Word"
  assertTrue (!(unary .integerToWord (.word Word.zero)).check)
    "integerToWord must require an Integer"
  assertTrue (!( { resultType := .integer, body := .bool true } : Program).check)
    "Integer result annotation must be checked"
  let hostBad : Program := { resultType := .word, body := .apply (.var 0) (.integer 0) }
  assertTrue (!hostBad.checkHost) "storageRead retains its Word parameter ABI"
  let hostConverted : Program := {
    resultType := .word
    body := .apply (.var 0) (.unary .integerToWord (.integer (-1))) }
  assertTrue hostConverted.checkHost "Integer may reach Word host functions through explicit conversion"
  match hostConverted.runHostStateful 20 with
  | .suspended suspension _ =>
      assertTrue (suspension.request == .storageRead (Word.ofIntModulo (-1)))
        "host request must contain the converted Word"
  | other => throw (IO.userError s!"expected converted Word host request, got {reprStr other}")

end Tests.CoreIntegers
end

section
-- leanmerge: from Solcore.Test.CoreLogicalShifts
/-! Focused proof and runtime regressions for bounded logical word shifts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def three : Word := Word.ofNatModulo 3
private def four : Word := Word.ofNatModulo 4
private def six : Word := Word.ofNatModulo 6
private def eight : Word := Word.ofNatModulo 8
private def sixteen : Word := Word.ofNatModulo 16
private def shift255_variant : Word := Word.ofNatModulo 255
private def shift256_variant : Word := Word.ofNatModulo 256
private def highBit_variant2 : Word := Word.ofNatModulo (2 ^ 255)

example : one_variant.shiftLeft zero = one_variant := Word.shiftLeft_zero one_variant
example : Word.maximum.shiftRight zero = Word.maximum :=
  Word.shiftRight_zero Word.maximum
example : one_variant.shiftLeft three = one_variant <<< three :=
  Word.shiftLeft_of_lt_256 one_variant three (by decide)
example : Word.maximum.shiftRight three = Word.maximum >>> three :=
  Word.shiftRight_of_lt_256 Word.maximum three (by decide)
example : one_variant.shiftLeft shift256_variant = zero :=
  Word.shiftLeft_of_ge_256 one_variant shift256_variant (by decide)
example : Word.maximum.shiftRight Word.maximum = zero :=
  Word.shiftRight_of_ge_256 Word.maximum Word.maximum (by decide)

example : BinaryOp.wordShl.apply (.word one_variant) (.word three) =
    some (.word (one_variant.shiftLeft three)) :=
  BinaryOp.apply_wordShl one_variant three
example : BinaryOp.wordShr.apply (.word eight) (.word one_variant) =
    some (.word (eight.shiftRight one_variant)) :=
  BinaryOp.apply_wordShr eight one_variant

example : Evaluates [] [] (.binary .wordShl (.word one_variant) (.word three))
    (.word (one_variant.shiftLeft three)) [] :=
  Evaluates.wordShl .word .word
example : Evaluates [] [] (.binary .wordShl (.word one_variant) (.word three))
    (.word (one_variant <<< three)) [] :=
  Evaluates.wordShl_lt_256 (by decide) .word .word
example : Evaluates [] [] (.binary .wordShl (.word one_variant) (.word shift256_variant))
    (.word zero) [] :=
  Evaluates.wordShl_ge_256 (by decide) .word .word
example : Evaluates [] [] (.binary .wordShr (.word eight) (.word one_variant))
    (.word (eight.shiftRight one_variant)) [] :=
  Evaluates.wordShr .word .word
example : Evaluates [] [] (.binary .wordShr (.word eight) (.word one_variant))
    (.word (eight >>> one_variant)) [] :=
  Evaluates.wordShr_lt_256 (by decide) .word .word
example : Evaluates [] []
    (.binary .wordShr (.word Word.maximum) (.word Word.maximum))
    (.word zero) [] :=
  Evaluates.wordShr_ge_256 (by decide) .word .word

private def testValuesTypesAndLiteralFuel_variant5 : IO Unit := do
  let cases : List (String × BinaryOp × Word × Word × Word) := [
    ("one shl three", .wordShl, one_variant, three, eight),
    ("three shl one", .wordShl, three, one_variant, six),
    ("eight shr one", .wordShr, eight, one_variant, four),
    ("one shr eight", .wordShr, one_variant, eight, zero),
    ("maximum shl zero", .wordShl, Word.maximum, zero, Word.maximum),
    ("maximum shr zero", .wordShr, Word.maximum, zero, Word.maximum),
    ("one shl 255", .wordShl, one_variant, shift255_variant, highBit_variant2),
    ("maximum shr 255", .wordShr, Word.maximum, shift255_variant, one_variant),
    ("one shl 256", .wordShl, one_variant, shift256_variant, zero),
    ("maximum shr 256", .wordShr, Word.maximum, shift256_variant, zero),
    ("zero shl maximum", .wordShl, zero, Word.maximum, zero),
    ("zero shr maximum", .wordShr, zero, Word.maximum, zero)
  ]
  for (name, op, value, shift, expected) in cases do
    let witness := wordProgram_variant (.binary op (.word value) (.word shift))
    assertTrue witness.check s!"{name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"{name} failed at the literal binary fuel boundary"

  for op in [BinaryOp.wordShl, .wordShr] do
    for body in [
        Expr.binary op .unit (.word one_variant),
        Expr.binary op (.word one_variant) .unit
      ] do
      assertTrue (!(wordProgram_variant body).check)
        s!"{reprStr op} accepted a non-word operand: {reprStr body}"

    let body := Expr.binary op (.word one_variant) (.word three)
    let wrongResult : Program := { resultType := .bool, body }
    assertTrue (!wrongResult.check)
      s!"{reprStr op} was accepted with a bool result"

    assertTrue
      ((wordProgram_variant (.binary op .unit (.word one_variant))).run 5 ==
        .fault (.invalidBinaryOperands op .unit (.word one_variant)))
      s!"raw {reprStr op} did not expose its invalid left operand"
    assertTrue
      ((wordProgram_variant (.binary op (.word one_variant) .unit)).run 5 ==
        .fault (.invalidBinaryOperands op (.word one_variant) .unit))
      s!"raw {reprStr op} did not expose its invalid right operand"

private def testFaultOrder_variant8 : IO Unit := do
  let rightWithEffect := allocatingWritingWord_variant zero one_variant shift256_variant
  for op in [BinaryOp.wordShl, .wordShr] do
    let body := Expr.binary op (.var 99) rightWithEffect
    match (wordProgram_variant body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated its shift after a value fault"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord_variant zero one_variant eight
  for op in [BinaryOp.wordShl, .wordShr] do
    let body := Expr.binary op leftWithEffect (.var 100)
    match (wordProgram_variant body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one_variant])
          s!"{reprStr op} shift fault did not observe the value store"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands_variant4 : IO Unit := do
  let cases : List (String × BinaryOp × Word × Word × Word) := [
    ("wordShl in range", .wordShl, eight, one_variant, sixteen),
    ("wordShr in range", .wordShr, eight, one_variant, four),
    ("wordShl oversized", .wordShl, one_variant, shift256_variant, zero),
    ("wordShr oversized", .wordShr, Word.maximum, shift256_variant, zero)
  ]
  for (name, op, value, shift, expected) in cases do
    let left := allocatingWritingWord_variant zero one_variant value
    let right := allocatingWritingWord_variant zero two_variant shift
    let witness := wordProgram_variant (.binary op left right)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.word expected) [.word one_variant, .word two_variant])
      s!"{name} did not evaluate value then shift exactly once"

/-- Cover all fourteen theorems plus values, order, faults, effects, and fuel. -/
def testCoreLogicalShifts : IO Unit := do
  testValuesTypesAndLiteralFuel_variant5
  testFaultOrder_variant8
  testEffectfulOperands_variant4

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreModularArithmetic
/-! Focused proof and runtime regressions for modular word arithmetic. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def seven : Word := Word.ofNatModulo 7
private def ten : Word := Word.ofNatModulo 10
private def twentyOne : Word := Word.ofNatModulo 21

example : seven.add zero = seven := Word.add_zero seven
example : Word.maximum.add one_variant = zero := Word.add_maximum_one
example : seven.sub zero = seven := Word.sub_zero seven
example : seven.sub seven = zero := Word.sub_self seven
example : zero.sub one_variant = Word.maximum := Word.zero_sub_one
example : seven.mul zero = zero := Word.mul_zero seven
example : seven.mul one_variant = seven := Word.mul_one seven
example : Word.maximum.mul two_variant = Word.ofNatModulo (wordModulus - 2) :=
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

private def testValuesTypesAndLiteralFuel_variant6 : IO Unit := do
  let underflow := Word.ofNatModulo (wordModulus - 4)
  let doubledMaximum := Word.ofNatModulo (wordModulus - 2)
  let highBit := Word.ofNatModulo (2 ^ 255)
  let cases : List (String × BinaryOp × Word × Word × Word) := [
    ("seven add three", .wordAdd, seven, three, ten),
    ("seven sub three", .wordSub, seven, three, four),
    ("three sub seven", .wordSub, three, seven, underflow),
    ("seven mul three", .wordMul, seven, three, twentyOne),
    ("maximum add one", .wordAdd, Word.maximum, one_variant, zero),
    ("zero sub one", .wordSub, zero, one_variant, Word.maximum),
    ("maximum mul two", .wordMul, Word.maximum, two_variant, doubledMaximum),
    ("zero add maximum", .wordAdd, zero, Word.maximum, Word.maximum),
    ("maximum sub maximum", .wordSub, Word.maximum, Word.maximum, zero),
    ("maximum mul zero", .wordMul, Word.maximum, zero, zero),
    ("high bit mul two", .wordMul, highBit, two_variant, zero)
  ]
  for (name, op, left, right, expected) in cases do
    let witness := wordProgram_variant (.binary op (.word left) (.word right))
    assertTrue witness.check s!"{name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"{name} failed at the literal binary fuel boundary"

  for op in [BinaryOp.wordAdd, .wordSub, .wordMul] do
    for body in [
        Expr.binary op .unit (.word one_variant),
        Expr.binary op (.word one_variant) .unit
      ] do
      assertTrue (!(wordProgram_variant body).check)
        s!"{reprStr op} accepted a non-word operand: {reprStr body}"

    let body := Expr.binary op (.word seven) (.word three)
    let wrongResult : Program := { resultType := .bool, body }
    assertTrue (!wrongResult.check)
      s!"{reprStr op} was accepted with a bool result"

    assertTrue
      ((wordProgram_variant (.binary op .unit (.word one_variant))).run 5 ==
        .fault (.invalidBinaryOperands op .unit (.word one_variant)))
      s!"raw {reprStr op} did not expose its invalid left operand"
    assertTrue
      ((wordProgram_variant (.binary op (.word one_variant) .unit)).run 5 ==
        .fault (.invalidBinaryOperands op (.word one_variant) .unit))
      s!"raw {reprStr op} did not expose its invalid right operand"

private def testFaultOrder_variant9 : IO Unit := do
  let rightWithEffect := allocatingWritingWord_variant zero one_variant three
  for op in [BinaryOp.wordAdd, .wordSub, .wordMul] do
    let body := Expr.binary op (.var 99) rightWithEffect
    match (wordProgram_variant body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated its right operand after a left fault"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord_variant zero one_variant seven
  for op in [BinaryOp.wordAdd, .wordSub, .wordMul] do
    let body := Expr.binary op leftWithEffect (.var 100)
    match (wordProgram_variant body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one_variant])
          s!"{reprStr op} right fault did not observe the left store"
    | result =>
        throw (IO.userError
          s!"{reprStr op} exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands_variant5 : IO Unit := do
  let cases : List (String × BinaryOp × Word) := [
    ("wordAdd", .wordAdd, ten),
    ("wordSub", .wordSub, four),
    ("wordMul", .wordMul, twentyOne)
  ]
  for (name, op, expected) in cases do
    let left := allocatingWritingWord_variant zero one_variant seven
    let right := allocatingWritingWord_variant zero two_variant three
    let witness := wordProgram_variant (.binary op left right)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.word expected) [.word one_variant, .word two_variant])
      s!"{name} did not evaluate left then right exactly once"

/-- Cover all fourteen theorems plus values, order, faults, effects, and fuel. -/
def testCoreModularArithmetic : IO Unit := do
  testValuesTypesAndLiteralFuel_variant6
  testFaultOrder_variant9
  testEffectfulOperands_variant5

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreModularExponentiation
/-! Focused proof and runtime regressions for internal modular exponentiation. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def thirtySeven : Word := word 37
private def highBit_variant3 : Word := word (2 ^ 255)

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

private def testValuesTypesAndLiteralFuel_variant7 : IO Unit := do
  -- Expected large-exponent values are algebraic boundaries, not giant Nat powers.
  let cases : List (String × Word × Word × Word) := [
    ("zero to zero", zero, zero, one),
    ("thirty-seven to zero", thirtySeven, zero, one),
    ("zero to one", zero, one, zero),
    ("one to maximum", one, Word.maximum, one),
    ("thirty-seven to one", thirtySeven, one, thirtySeven),
    ("two to eight", two, word 8, word 256),
    ("two to 256", two, word 256, zero),
    ("high bit squared", highBit_variant3, two, zero),
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

private def testFaultOrder_variant10 : IO Unit := do
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

private def testEffectfulOperands_variant6 : IO Unit := do
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
  testValuesTypesAndLiteralFuel_variant7
  testFaultOrder_variant10
  testEffectfulOperands_variant6

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreSignExtension
/-! Focused proof and runtime regressions for internal word sign extension. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def two_variant3 : Word := word 2

example : (word 0).signExtend (word 0x7f) = word 0x7f :=
  Word.signExtend_clear (word 0) (word 0x7f) (by decide) (by decide)
example : (word 0).signExtend (word 0x80) = word (wordModulus - 128) :=
  Word.signExtend_set (word 0) (word 0x80) (by decide) (by decide)
example : (word 32).signExtend (word 0x1122) = word 0x1122 :=
  Word.signExtend_ge_32 (word 32) (word 0x1122) (by decide)
example : (word 7).signExtend zero = zero := Word.signExtend_zero (word 7)
example : (word 31).signExtend (word 0x1122) = word 0x1122 :=
  Word.signExtend_index31 (word 0x1122)

example : BinaryOp.wordSignExtend.apply (.word (word 0)) (.word (word 0x80)) =
    some (.word ((word 0).signExtend (word 0x80))) :=
  BinaryOp.apply_wordSignExtend (word 0) (word 0x80)
example : Evaluates [] []
    (.binary .wordSignExtend (.word (word 0)) (.word (word 0x80)))
    (.word ((word 0).signExtend (word 0x80))) [] :=
  Evaluates.wordSignExtend .word .word
example : Evaluates [] []
    (.binary .wordSignExtend (.word (word 0)) (.word (word 0x7f)))
    (.word (word 0x7f)) [] :=
  Evaluates.wordSignExtend_clear (by decide) (by decide) .word .word
example : Evaluates [] []
    (.binary .wordSignExtend (.word (word 0)) (.word (word 0x80)))
    (.word (word (wordModulus - 128))) [] :=
  Evaluates.wordSignExtend_set (by decide) (by decide) .word .word
example : Evaluates [] []
    (.binary .wordSignExtend (.word (word 32)) (.word (word 0x1122)))
    (.word (word 0x1122)) [] :=
  Evaluates.wordSignExtend_ge_32 (by decide) .word .word

private def testValuesTypesAndFuel_variant5 : IO Unit := do
  let arbitrary := word 0x123456
  let cases : List (String × Word × Word × Word) := [
    ("index 0 clear", word 0, word 0x7f, word 0x7f),
    ("index 0 set", word 0, word 0x80, word (wordModulus - 128)),
    ("index 0 ff", word 0, word 0xff, Word.maximum),
    ("index 0 truncates clear", word 0, word 0x1234, word 0x34),
    ("index 0 truncates set", word 0, word 0x1280, word (wordModulus - 128)),
    ("index 1 clear", word 1, word 0x7fff, word 0x7fff),
    ("index 1 set", word 1, word 0x8000, word (wordModulus - 32768)),
    ("index 31 zero", word 31, zero, zero),
    ("index 31 maximum", word 31, Word.maximum, Word.maximum),
    ("index 31 arbitrary", word 31, arbitrary, arbitrary),
    ("index 32 identity", word 32, arbitrary, arbitrary),
    ("maximum index identity", Word.maximum, arbitrary, arbitrary)
  ]
  for (name, index, value, expected) in cases do
    let witness := wordProgram_variant2 (.binary .wordSignExtend (.word index) (.word value))
    assertTrue witness.check s!"wordSignExtend {name} failed to type-check"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordSignExtend {name} finished below exact fuel"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"wordSignExtend {name} failed at exact fuel"

  let validBody : Expr :=
    .binary .wordSignExtend (.word (word 0)) (.word (word 0x80))
  let wrongResult : Program := { resultType := .bool, body := validBody }
  assertTrue (!wrongResult.check) "wordSignExtend accepted bool result"
  let wrongLeft : Expr := .binary .wordSignExtend .unit (.word (word 0x80))
  let wrongRight : Expr := .binary .wordSignExtend (.word zero) .unit
  assertTrue (!(wordProgram_variant2 wrongLeft).check) "wordSignExtend accepted bad index"
  assertTrue (!(wordProgram_variant2 wrongRight).check) "wordSignExtend accepted bad value"
  assertTrue ((wordProgram_variant2 wrongLeft).run 5 ==
    .fault (.invalidBinaryOperands .wordSignExtend .unit (.word (word 0x80))))
    "wordSignExtend invalid left payload changed"
  assertTrue ((wordProgram_variant2 wrongRight).run 5 ==
    .fault (.invalidBinaryOperands .wordSignExtend (.word zero) .unit))
    "wordSignExtend invalid right payload changed"

private def testFaultOrder_variant11 : IO Unit := do
  let effectfulValue := allocatingWritingWord zero one (word 0x80)
  match (wordProgram_variant2 (.binary .wordSignExtend (.var 99) effectfulValue)).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty "wordSignExtend evaluated value after index fault"
  | result => throw (IO.userError s!"wordSignExtend wrong index fault: {reprStr result}")

  let effectfulIndex := allocatingWritingWord zero one zero
  match (wordProgram_variant2 (.binary .wordSignExtend effectfulIndex (.var 100))).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordSignExtend value fault did not retain index store"
  | result => throw (IO.userError s!"wordSignExtend wrong value fault: {reprStr result}")

private def testEffects_variant2 : IO Unit := do
  let index := allocatingWritingWord zero one zero
  let value := allocatingWritingWord zero two_variant3 (word 0x80)
  let witness := wordProgram_variant2 (.binary .wordSignExtend index value)
  assertTrue witness.check "effectful wordSignExtend failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordSignExtend finished below exact fuel"
  assertTrue (witness.runStateful 29 ==
    .done (.word (word (wordModulus - 128))) [.word one, .word two_variant3])
    "wordSignExtend did not evaluate index then value once or retain final store"

/-- Cover all ten theorems plus values, types, faults, effects, store, and fuel. -/
def testCoreSignExtension : IO Unit := do
  testValuesTypesAndFuel_variant5
  testFaultOrder_variant11
  testEffects_variant2

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreSignedComparison
/-! Focused proof and runtime regressions for internal signed word comparison. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def positiveMaximum_variant3 : Word := word (2 ^ 255 - 1)

example : zero.signedGt zero = false := Word.signedGt_self zero
example : one.signedGt zero = decide (one > zero) :=
  Word.signedGt_both_nonnegative one zero (by decide) (by decide)
example : Word.maximum.signedGt highBit =
    decide (Word.maximum > highBit) :=
  Word.signedGt_both_negative Word.maximum highBit (by decide) (by decide)
example : zero.signedGt Word.maximum = true :=
  Word.signedGt_nonnegative_negative zero Word.maximum (by decide) (by decide)
example : Word.maximum.signedGt zero = false :=
  Word.signedGt_negative_nonnegative Word.maximum zero (by decide) (by decide)

example : BinaryOp.wordSgt.apply (.word one) (.word zero) =
    some (.bool (one.signedGt zero)) :=
  BinaryOp.apply_wordSgt one zero
example : Evaluates [] [] (.binary .wordSgt (.word one) (.word zero))
    (.bool (one.signedGt zero)) [] :=
  Evaluates.wordSgt .word .word
example : Evaluates [] [] (.binary .wordSgt (.word one) (.word zero))
    (.bool true) [] :=
  Evaluates.wordSgt_both_nonnegative (by decide) (by decide) .word .word
example : Evaluates [] []
    (.binary .wordSgt (.word Word.maximum) (.word highBit))
    (.bool true) [] :=
  Evaluates.wordSgt_both_negative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSgt (.word zero) (.word Word.maximum))
    (.bool true) [] :=
  Evaluates.wordSgt_nonnegative_negative (by decide) (by decide) .word .word
example : Evaluates [] [] (.binary .wordSgt (.word highBit) (.word zero))
    (.bool false) [] :=
  Evaluates.wordSgt_negative_nonnegative (by decide) (by decide) .word .word

private def testValuesTypesAndLiteralFuel_variant8 : IO Unit := do
  let cases : List (String × Word × Word × Bool) := [
    ("zero above zero", zero, zero, false),
    ("one above zero", one, zero, true),
    ("zero above one", zero, one, false),
    ("positive maximum above zero", positiveMaximum_variant3, zero, true),
    ("zero above positive maximum", zero, positiveMaximum_variant3, false),
    ("high bit above zero", highBit, zero, false),
    ("zero above maximum", zero, Word.maximum, true),
    ("maximum above zero", Word.maximum, zero, false),
    ("maximum above high bit", Word.maximum, highBit, true),
    ("high bit above maximum", highBit, Word.maximum, false),
    ("maximum above maximum", Word.maximum, Word.maximum, false)
  ]
  for (name, left, right, expected) in cases do
    let witness := boolProgram (.binary .wordSgt (.word left) (.word right))
    assertTrue witness.check s!"wordSgt {name} failed to type-check as bool"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"wordSgt {name} finished below the literal fuel boundary"
    assertTrue (witness.run 5 == .done (.bool expected))
      s!"wordSgt {name} failed at the literal fuel boundary"

  let validBody : Expr := .binary .wordSgt (.word one) (.word zero)
  let wrongResult : Program := { resultType := .word, body := validBody }
  assertTrue (!wrongResult.check) "wordSgt accepted a word result type"

  let wrongLeft : Expr := .binary .wordSgt .unit (.word zero)
  let wrongRight : Expr := .binary .wordSgt (.word one) .unit
  assertTrue (!(boolProgram wrongLeft).check) "wordSgt accepted a non-word left"
  assertTrue (!(boolProgram wrongRight).check) "wordSgt accepted a non-word right"
  assertTrue
    ((boolProgram wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands .wordSgt .unit (.word zero)))
    "raw wordSgt did not expose its invalid left operand"
  assertTrue
    ((boolProgram wrongRight).run 5 ==
      .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "raw wordSgt did not expose its invalid right operand"

private def testFaultOrder_variant12 : IO Unit := do
  let effectfulRight := allocatingWritingWord zero one Word.maximum
  let leftFault : Expr := .binary .wordSgt (.var 99) effectfulRight
  match (boolProgram leftFault).runStateful 8 with
  | .fault (.unboundVariable 99) state =>
      assertTrue state.store.isEmpty
        "wordSgt evaluated right after a left fault"
  | result =>
      throw (IO.userError s!"wordSgt exposed the wrong left fault: {reprStr result}")

  let effectfulLeft := allocatingWritingWord zero one zero
  let rightFault : Expr := .binary .wordSgt effectfulLeft (.var 100)
  match (boolProgram rightFault).runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one])
        "wordSgt right fault did not observe the left store"
  | result =>
      throw (IO.userError s!"wordSgt exposed the wrong right fault: {reprStr result}")

private def testEffectfulOperands_variant7 : IO Unit := do
  let left := allocatingWritingWord zero one zero
  let right := allocatingWritingWord zero two Word.maximum
  let witness := boolProgram (.binary .wordSgt left right)
  assertTrue witness.check "effectful wordSgt failed to type-check"
  assertTrue (witness.run 28 == .outOfFuel)
    "effectful wordSgt finished below exact fuel"
  assertTrue
    (witness.runStateful 29 == .done (.bool true) [.word one, .word two])
    "wordSgt did not evaluate left then right exactly once or retain the store"

/-- Cover all eleven theorems plus signed values, types, faults, effects, and fuel. -/
def testCoreSignedComparison : IO Unit := do
  testValuesTypesAndLiteralFuel_variant8
  testFaultOrder_variant12
  testEffectfulOperands_variant7

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreSignedComparisonFlags
/-! Focused proof and runtime regressions for signed word comparison flags. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def positiveMaximum_variant4 : Word := word (2 ^ 255 - 1)

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

private def testValuesTypesAndFuel_variant6 : IO Unit := do
  let cases : List (String × Word × Word × Word × Word) := [
    ("zero one", zero, one, zero, one),
    ("one zero", one, zero, one, zero),
    ("positive maximum zero", positiveMaximum_variant4, zero, one, zero),
    ("zero positive maximum", zero, positiveMaximum_variant4, zero, one),
    ("maximum high bit", Word.maximum, highBit, one, zero),
    ("high bit maximum", highBit, Word.maximum, zero, one),
    ("zero maximum", zero, Word.maximum, one, zero),
    ("maximum zero", Word.maximum, zero, zero, one),
    ("maximum equal", Word.maximum, Word.maximum, zero, zero)
  ]
  for (name, left, right, sgtExpected, sltExpected) in cases do
    let sgt := wordProgram_variant2 (Expr.wordSgtFlag (.word left) (.word right))
    let slt := wordProgram_variant2 (Expr.wordSltFlag (.word left) (.word right))
    assertTrue (sgt.check && slt.check) s!"signed flags {name} failed to type-check"
    assertTrue (sgt.run 7 == .outOfFuel && sgt.run 8 == .done (.word sgtExpected))
      s!"wordSgtFlag {name} missed exact 7/8 fuel"
    assertTrue (slt.run 13 == .outOfFuel && slt.run 14 == .done (.word sltExpected))
      s!"wordSltFlag {name} missed exact 13/14 fuel"

  for body in [Expr.wordSgtFlag .unit (.word zero),
      Expr.wordSgtFlag (.word one) .unit,
      Expr.wordSltFlag .unit (.word zero), Expr.wordSltFlag (.word one) .unit] do
    assertTrue (!(wordProgram_variant2 body).check) "signed flag accepted a non-word operand"
  let wrongSgt : Program := {
    resultType := .bool
    body := Expr.wordSgtFlag (.word one) (.word zero)
  }
  let wrongSlt : Program := {
    resultType := .bool
    body := Expr.wordSltFlag (.word zero) (.word one)
  }
  assertTrue (!wrongSgt.check && !wrongSlt.check) "signed flag accepted bool result"

  assertTrue ((wordProgram_variant2 (Expr.wordSgtFlag .unit (.word one))).run 8 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "wordSgtFlag invalid payload was not direct"
  assertTrue ((wordProgram_variant2 (Expr.wordSltFlag .unit (.word one))).run 14 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSltFlag invalid payload was not swapped"
  assertTrue ((wordProgram_variant2 (Expr.wordSgtFlag (.word one) .unit)).run 8 ==
    .fault (.invalidBinaryOperands .wordSgt (.word one) .unit))
    "wordSgtFlag invalid right payload was not direct"
  assertTrue ((wordProgram_variant2 (Expr.wordSltFlag (.word one) .unit)).run 14 ==
    .fault (.invalidBinaryOperands .wordSgt .unit (.word one)))
    "wordSltFlag invalid right payload was not swapped"

private def testFaultOrder_variant13 : IO Unit := do
  let effectfulRight := allocatingWritingWord zero one Word.maximum
  for (name, body) in [("sgt", Expr.wordSgtFlag (.var 99) effectfulRight),
      ("slt", Expr.wordSltFlag (.var 99) effectfulRight)] do
    match (wordProgram_variant2 body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty s!"{name} evaluated right after left fault"
    | result => throw (IO.userError s!"{name} wrong left fault: {reprStr result}")

  let effectfulLeft := allocatingWritingWord zero one Word.maximum
  let sgtRightFault := wordProgram_variant2 (Expr.wordSgtFlag effectfulLeft (.var 100))
  let sltRightFault := wordProgram_variant2 (Expr.wordSltFlag effectfulLeft (.var 100))
  match sgtRightFault.runStateful 64 with
  | .fault (.unboundVariable 100) state =>
      assertTrue (state.store == [.word one]) "sgt right fault lost left store"
  | result => throw (IO.userError s!"sgt wrong right fault: {reprStr result}")
  match sltRightFault.runStateful 64 with
  | .fault (.unboundVariable 101) state =>
      assertTrue (state.store == [.word one]) "slt right fault lost left store"
  | result => throw (IO.userError s!"slt wrong weakened fault: {reprStr result}")

private def testEffects_variant3 : IO Unit := do
  let left := allocatingWritingWord zero one Word.maximum
  let right := allocatingWritingWord zero (word 2) zero
  let sgt := wordProgram_variant2 (Expr.wordSgtFlag left right)
  let slt := wordProgram_variant2 (Expr.wordSltFlag left right)
  assertTrue (sgt.run 31 == .outOfFuel &&
    sgt.runStateful 32 == .done (.word zero) [.word one, .word (word 2)])
    "wordSgtFlag missed exact effect/store boundary"
  assertTrue (slt.run 37 == .outOfFuel &&
    slt.runStateful 38 == .done (.word one) [.word one, .word (word 2)])
    "wordSltFlag missed exact effect/store boundary"

/-- Cover all twenty theorems plus signed values, types, faults, effects, and fuel. -/
def testCoreSignedComparisonFlags : IO Unit := do
  testValuesTypesAndFuel_variant6
  testFaultOrder_variant13
  testEffects_variant3

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreSignedDivision
/-! Focused proof and runtime regressions for signed division and modulo. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def neg (magnitude : Nat) : Word := word (wordModulus - magnitude)
private def three_variant : Word := word 3
private def seven_variant : Word := word 7
private def negativeOne : Word := Word.maximum
private def minimum : Word := word (2 ^ 255)

example : seven_variant.sdiv zero = zero := Word.sdiv_zero seven_variant
example : seven_variant.sdiv three_variant =
    Word.ofSignedMagnitude (seven_variant.signedNegative != three_variant.signedNegative)
      (seven_variant.signedMagnitude / three_variant.signedMagnitude) :=
  Word.sdiv_nonzero seven_variant three_variant (by decide)
example : seven_variant.smod zero = zero := Word.smod_zero seven_variant
example : seven_variant.smod three_variant =
    Word.ofSignedMagnitude seven_variant.signedNegative
      (seven_variant.signedMagnitude % three_variant.signedMagnitude) :=
  Word.smod_nonzero seven_variant three_variant (by decide)
example : minimum.sdiv negativeOne = minimum :=
  Word.sdiv_minimum_negative_one
example : minimum.smod negativeOne = zero :=
  Word.smod_minimum_negative_one

example : BinaryOp.wordSdiv.apply (.word seven_variant) (.word three_variant) =
    some (.word (seven_variant.sdiv three_variant)) := BinaryOp.apply_wordSdiv seven_variant three_variant
example : BinaryOp.wordSmod.apply (.word seven_variant) (.word three_variant) =
    some (.word (seven_variant.smod three_variant)) := BinaryOp.apply_wordSmod seven_variant three_variant

example : Evaluates [] [] (.binary .wordSdiv (.word seven_variant) (.word three_variant))
    (.word (seven_variant.sdiv three_variant)) [] := Evaluates.wordSdiv .word .word
example : Evaluates [] [] (.binary .wordSdiv (.word seven_variant) (.word zero))
    (.word zero) [] := Evaluates.wordSdiv_zero .word .word
example : Evaluates [] [] (.binary .wordSdiv (.word seven_variant) (.word three_variant))
    (.word (Word.ofSignedMagnitude false two.val)) [] :=
  Evaluates.wordSdiv_nonzero (by decide) .word .word
example : Evaluates [] [] (.binary .wordSmod (.word seven_variant) (.word three_variant))
    (.word (seven_variant.smod three_variant)) [] := Evaluates.wordSmod .word .word
example : Evaluates [] [] (.binary .wordSmod (.word seven_variant) (.word zero))
    (.word zero) [] := Evaluates.wordSmod_zero .word .word
example : Evaluates [] [] (.binary .wordSmod (.word seven_variant) (.word three_variant))
    (.word (Word.ofSignedMagnitude false one.val)) [] :=
  Evaluates.wordSmod_nonzero (by decide) .word .word

private def testValuesTypesAndFuel_variant7 : IO Unit := do
  let negativeTwo := neg 2
  let negativeThree := neg 3
  let negativeSeven := neg 7
  let cases : List (String × BinaryOp × Word × Word × Word) := [
    ("7 / 3", .wordSdiv, seven_variant, three_variant, two),
    ("7 / -3", .wordSdiv, seven_variant, negativeThree, negativeTwo),
    ("-7 / 3", .wordSdiv, negativeSeven, three_variant, negativeTwo),
    ("-7 / -3", .wordSdiv, negativeSeven, negativeThree, two),
    ("7 % 3", .wordSmod, seven_variant, three_variant, one),
    ("7 % -3", .wordSmod, seven_variant, negativeThree, one),
    ("-7 % 3", .wordSmod, negativeSeven, three_variant, negativeOne),
    ("-7 % -3", .wordSmod, negativeSeven, negativeThree, negativeOne),
    ("zero numerator div", .wordSdiv, zero, three_variant, zero),
    ("zero numerator mod", .wordSmod, zero, three_variant, zero),
    ("zero divisor div", .wordSdiv, seven_variant, zero, zero),
    ("zero divisor mod", .wordSmod, seven_variant, zero, zero),
    ("zero div zero", .wordSdiv, zero, zero, zero),
    ("zero mod zero", .wordSmod, zero, zero, zero),
    ("minimum / -1", .wordSdiv, minimum, negativeOne, minimum),
    ("minimum % -1", .wordSmod, minimum, negativeOne, zero),
    ("minimum / 1", .wordSdiv, minimum, one, minimum),
    ("minimum % 1", .wordSmod, minimum, one, zero),
    ("-1 / minimum", .wordSdiv, negativeOne, minimum, zero),
    ("-1 % minimum", .wordSmod, negativeOne, minimum, negativeOne),
    ("equal magnitude negative/positive", .wordSdiv, negativeSeven, seven_variant,
      negativeOne),
    ("equal magnitude positive/negative", .wordSdiv, seven_variant, negativeSeven,
      negativeOne),
    ("equal magnitude remainder", .wordSmod, negativeSeven, seven_variant, zero)
  ]
  for (name, operation, dividend, divisor, expected) in cases do
    let witness := wordProgram_variant2
      (.binary operation (.word dividend) (.word divisor))
    assertTrue witness.check s!"{name} failed to type-check"
    assertTrue (witness.run 4 == .outOfFuel) s!"{name} finished below fuel 5"
    assertTrue (witness.run 5 == .done (.word expected))
      s!"{name} produced the wrong signed result"

  for operation in [BinaryOp.wordSdiv, BinaryOp.wordSmod] do
    let valid := Expr.binary operation (.word seven_variant) (.word three_variant)
    let wrongResult : Program := { resultType := .bool, body := valid }
    assertTrue (!wrongResult.check) "signed operation accepted bool result"
    let wrongLeft := Expr.binary operation .unit (.word one)
    let wrongRight := Expr.binary operation (.word one) .unit
    assertTrue (!(wordProgram_variant2 wrongLeft).check) "accepted nonword dividend"
    assertTrue (!(wordProgram_variant2 wrongRight).check) "accepted nonword divisor"
    assertTrue ((wordProgram_variant2 wrongLeft).run 5 ==
      .fault (.invalidBinaryOperands operation .unit (.word one)))
      "invalid dividend payload changed"
    assertTrue ((wordProgram_variant2 wrongRight).run 5 ==
      .fault (.invalidBinaryOperands operation (.word one) .unit))
      "invalid divisor payload changed"

private def testFaultOrder_variant14 : IO Unit := do
  let rightEffect := allocatingWritingWord zero one three_variant
  for operation in [BinaryOp.wordSdiv, BinaryOp.wordSmod] do
    match (wordProgram_variant2 (.binary operation (.var 99) rightEffect)).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty "divisor ran after dividend fault"
    | result => throw (IO.userError s!"wrong dividend fault: {reprStr result}")

  let leftEffect := allocatingWritingWord zero one seven_variant
  for operation in [BinaryOp.wordSdiv, BinaryOp.wordSmod] do
    match (wordProgram_variant2 (.binary operation leftEffect (.var 100))).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one])
          "divisor fault lost completed dividend store"
    | result => throw (IO.userError s!"wrong divisor fault: {reprStr result}")

private def testEffects_variant4 : IO Unit := do
  let dividend := allocatingWritingWord zero one (neg 7)
  for (name, operation, divisorResult, expected) in [
      ("nonzero sdiv", BinaryOp.wordSdiv, three_variant, neg 2),
      ("nonzero smod", BinaryOp.wordSmod, three_variant, negativeOne),
      ("zero sdiv", BinaryOp.wordSdiv, zero, zero),
      ("zero smod", BinaryOp.wordSmod, zero, zero) ] do
    let divisor := allocatingWritingWord zero two divisorResult
    let witness := wordProgram_variant2 (.binary operation dividend divisor)
    assertTrue witness.check s!"effectful {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel) s!"{name} finished below fuel 29"
    assertTrue (witness.runStateful 29 ==
      .done (.word expected) [.word one, .word two])
      s!"{name} did not evaluate dividend then divisor exactly once"

/-- Cover all fourteen theorems plus signed values, faults, effects, and fuel. -/
def testCoreSignedDivision : IO Unit := do
  testValuesTypesAndFuel_variant7
  testFaultOrder_variant14
  testEffects_variant4

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreTernaryModularArithmetic
/-! Focused proof and runtime regressions for ternary modular word arithmetic. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def four_variant : Word := word 4
private def five : Word := word 5
private def six_variant : Word := word 6
private def seven_variant2 : Word := word 7

example : seven_variant2.addMod three_variant zero = zero := Word.addMod_zero seven_variant2 three_variant
example : seven_variant2.addMod three_variant five =
    Word.ofNatModulo ((seven_variant2.val + three_variant.val) % five.val) :=
  Word.addMod_nonzero seven_variant2 three_variant five (by decide)
example : seven_variant2.mulMod three_variant zero = zero := Word.mulMod_zero seven_variant2 three_variant
example : seven_variant2.mulMod three_variant five =
    Word.ofNatModulo ((seven_variant2.val * three_variant.val) % five.val) :=
  Word.mulMod_nonzero seven_variant2 three_variant five (by decide)
example : Word.maximum.addMod one Word.maximum = one :=
  Word.addMod_no_prewrap
example : Word.maximum.mulMod Word.maximum Word.maximum = zero :=
  Word.mulMod_no_prewrap

example : TernaryOp.wordAddMod.apply
    (.word seven_variant2) (.word three_variant) (.word five) =
    some (.word (seven_variant2.addMod three_variant five)) :=
  TernaryOp.apply_wordAddMod seven_variant2 three_variant five
example : TernaryOp.wordMulMod.apply
    (.word seven_variant2) (.word three_variant) (.word five) =
    some (.word (seven_variant2.mulMod three_variant five)) :=
  TernaryOp.apply_wordMulMod seven_variant2 three_variant five

example : Evaluates [] []
    (.ternary .wordAddMod (.word seven_variant2) (.word three_variant) (.word five))
    (.word (seven_variant2.addMod three_variant five)) [] :=
  Evaluates.wordAddMod .word .word .word
example : Evaluates [] []
    (.ternary .wordAddMod (.word seven_variant2) (.word three_variant) (.word zero))
    (.word zero) [] :=
  Evaluates.wordAddMod_zero .word .word .word
example : Evaluates [] []
    (.ternary .wordAddMod (.word seven_variant2) (.word three_variant) (.word five))
    (.word (Word.ofNatModulo ((seven_variant2.val + three_variant.val) % five.val))) [] :=
  Evaluates.wordAddMod_nonzero (by decide) .word .word .word
example : Evaluates [] []
    (.ternary .wordMulMod (.word seven_variant2) (.word three_variant) (.word five))
    (.word (seven_variant2.mulMod three_variant five)) [] :=
  Evaluates.wordMulMod .word .word .word
example : Evaluates [] []
    (.ternary .wordMulMod (.word seven_variant2) (.word three_variant) (.word zero))
    (.word zero) [] :=
  Evaluates.wordMulMod_zero .word .word .word
example : Evaluates [] []
    (.ternary .wordMulMod (.word seven_variant2) (.word three_variant) (.word five))
    (.word (Word.ofNatModulo ((seven_variant2.val * three_variant.val) % five.val))) [] :=
  Evaluates.wordMulMod_nonzero (by decide) .word .word .word

private def testValuesTypesAndLiteralFuel_variant9 : IO Unit := do
  let cases : List (String × TernaryOp × Word × Word × Word × Word) := [
    ("ordinary addmod", .wordAddMod, seven_variant2, three_variant, six_variant, four_variant),
    ("ordinary mulmod", .wordMulMod, seven_variant2, three_variant, five, one),
    ("addmod modulus one", .wordAddMod, seven_variant2, three_variant, one, zero),
    ("mulmod modulus one", .wordMulMod, seven_variant2, three_variant, one, zero),
    ("addmod modulus zero", .wordAddMod, seven_variant2, three_variant, zero, zero),
    ("mulmod modulus zero", .wordMulMod, seven_variant2, three_variant, zero, zero),
    ("addmod without prewrap", .wordAddMod,
      Word.maximum, Word.maximum, Word.maximum, zero),
    ("mulmod without prewrap", .wordMulMod,
      Word.maximum, Word.maximum, Word.maximum, zero)
  ]
  for (name, op, first, second, modulus, expected) in cases do
    let witness := wordProgram_variant2
      (.ternary op (.word first) (.word second) (.word modulus))
    assertTrue witness.check s!"{name} failed to type-check"
    assertTrue (witness.run 6 == .outOfFuel)
      s!"{name} finished below the literal fuel boundary"
    assertTrue (witness.run 7 == .done (.word expected))
      s!"{name} failed at the literal fuel boundary"

  for op in [TernaryOp.wordAddMod, .wordMulMod] do
    let valid := Expr.ternary op (.word seven_variant2) (.word three_variant) (.word five)
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
      let witness := wordProgram_variant2 body
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

private def testFaultOrder_variant15 : IO Unit := do
  for op in [TernaryOp.wordAddMod, .wordMulMod] do
    let laterSecond := allocatingWritingWord zero two three_variant
    let laterModulus := allocatingWritingWord zero three_variant five
    match (wordProgram_variant2
        (.ternary op (.var 99) laterSecond laterModulus)).runStateful 64 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{reprStr op} evaluated operands after a first fault"
    | result => throw (IO.userError
        s!"{reprStr op} exposed the wrong first fault: {reprStr result}")

    let firstEffect := allocatingWritingWord zero one seven_variant2
    match (wordProgram_variant2
        (.ternary op firstEffect (.var 100) laterModulus)).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one])
          s!"{reprStr op} second fault lost or repeated the first effect"
    | result => throw (IO.userError
        s!"{reprStr op} exposed the wrong second fault: {reprStr result}")

    let secondEffect := allocatingWritingWord zero two three_variant
    match (wordProgram_variant2
        (.ternary op firstEffect secondEffect (.var 101))).runStateful 64 with
    | .fault (.unboundVariable 101) state =>
        assertTrue (state.store == [.word one, .word two])
          s!"{reprStr op} modulus fault lost or repeated earlier effects"
    | result => throw (IO.userError
        s!"{reprStr op} exposed the wrong modulus fault: {reprStr result}")

private def testEffectfulZeroModulus : IO Unit := do
  let first := allocatingWritingWord zero one Word.maximum
  let second := allocatingWritingWord zero two Word.maximum
  let modulus := allocatingWritingWord zero three_variant zero
  for op in [TernaryOp.wordAddMod, .wordMulMod] do
    let witness := wordProgram_variant2 (.ternary op first second modulus)
    assertTrue witness.check s!"effectful {reprStr op} failed to type-check"
    assertTrue (witness.run 42 == .outOfFuel)
      s!"effectful {reprStr op} finished below exact fuel"
    assertTrue
      (witness.runStateful 43 ==
        .done (.word zero) [.word one, .word two, .word three_variant])
      s!"{reprStr op} did not evaluate all operands once or retain the final store"

/-- Cover all fourteen theorems plus values, types, faults, effects, and fuel. -/
def testCoreTernaryModularArithmetic : IO Unit := do
  testValuesTypesAndLiteralFuel_variant9
  testFaultOrder_variant15
  testEffectfulZeroModulus

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreUnaryPrimitives
/-! Focused proof and runtime regressions for direct unary primitives. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def one_variant4 : Word := Word.ofNatModulo 1

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

example : Evaluates [] [] (.unary .wordNot (.word one_variant4))
    (.word one_variant4.bitNot) [] :=
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

private def testValuesTypesAndLiteralFuel_variant10 : IO Unit := do
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
    ("one", one_variant4, one_variant4.bitNot),
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
  let operand := allocatingWritingWord_variant zero one_variant4 zero
  let witness := program .word (.unary .wordNot operand)
  assertTrue witness.check "effectful wordNot failed to type-check"
  assertTrue (witness.run 14 == .outOfFuel)
    "effectful wordNot finished below its exact fuel boundary"
  assertTrue
    (witness.runStateful 15 == .done (.word Word.maximum) [.word one_variant4])
    "wordNot did not evaluate its operand exactly once or retain its final store"

/-- Cover every named unary theorem plus values, types, faults, effects, and fuel. -/
def testCoreUnaryPrimitives : IO Unit := do
  testValuesTypesAndLiteralFuel_variant10
  testRawFaults
  testEffectfulWordNot

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreUnsignedDivision
/-! Focused proof and runtime regressions for unsigned division and modulo. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def seven_variant3 : Word := Word.ofNatModulo 7

example : seven_variant3.udiv zero = zero := Word.udiv_zero seven_variant3
example : seven_variant3.umod zero = zero := Word.umod_zero seven_variant3
example : seven_variant3.udiv three = seven_variant3 / three :=
  Word.udiv_nonzero seven_variant3 three (by decide)
example : seven_variant3.umod three = seven_variant3 % three :=
  Word.umod_nonzero seven_variant3 three (by decide)

example : BinaryOp.wordDiv.apply (.word seven_variant3) (.word three) =
    some (.word (seven_variant3.udiv three)) :=
  BinaryOp.apply_wordDiv seven_variant3 three
example : BinaryOp.wordMod.apply (.word seven_variant3) (.word three) =
    some (.word (seven_variant3.umod three)) :=
  BinaryOp.apply_wordMod seven_variant3 three

example : Evaluates [] [] (.binary .wordDiv (.word seven_variant3) (.word three))
    (.word (seven_variant3.udiv three)) [] :=
  Evaluates.wordDiv .word .word
example : Evaluates [] [] (.binary .wordDiv (.word seven_variant3) (.word zero))
    (.word zero) [] :=
  Evaluates.wordDiv_zero .word .word
example : Evaluates [] [] (.binary .wordDiv (.word seven_variant3) (.word three))
    (.word (seven_variant3 / three)) [] :=
  Evaluates.wordDiv_nonzero (by decide) .word .word

example : Evaluates [] [] (.binary .wordMod (.word seven_variant3) (.word three))
    (.word (seven_variant3.umod three)) [] :=
  Evaluates.wordMod .word .word
example : Evaluates [] [] (.binary .wordMod (.word seven_variant3) (.word zero))
    (.word zero) [] :=
  Evaluates.wordMod_zero .word .word
example : Evaluates [] [] (.binary .wordMod (.word seven_variant3) (.word three))
    (.word (seven_variant3 % three)) [] :=
  Evaluates.wordMod_nonzero (by decide) .word .word

private def testValuesTypesAndLiteralFuel_variant11 : IO Unit := do
  let maximum := Word.maximum
  let cases : List (String × Program × Value) := [
    ("seven div three", wordProgram_variant
      (.binary .wordDiv (.word seven_variant3) (.word three)), .word two_variant),
    ("seven mod three", wordProgram_variant
      (.binary .wordMod (.word seven_variant3) (.word three)), .word one_variant),
    ("three div seven", wordProgram_variant
      (.binary .wordDiv (.word three) (.word seven_variant3)), .word zero),
    ("three mod seven", wordProgram_variant
      (.binary .wordMod (.word three) (.word seven_variant3)), .word three),
    ("zero numerator div", wordProgram_variant
      (.binary .wordDiv (.word zero) (.word three)), .word zero),
    ("zero numerator mod", wordProgram_variant
      (.binary .wordMod (.word zero) (.word three)), .word zero),
    ("zero divisor div", wordProgram_variant
      (.binary .wordDiv (.word seven_variant3) (.word zero)), .word zero),
    ("zero divisor mod", wordProgram_variant
      (.binary .wordMod (.word seven_variant3) (.word zero)), .word zero),
    ("zero div zero", wordProgram_variant
      (.binary .wordDiv (.word zero) (.word zero)), .word zero),
    ("zero mod zero", wordProgram_variant
      (.binary .wordMod (.word zero) (.word zero)), .word zero),
    ("one div maximum", wordProgram_variant
      (.binary .wordDiv (.word one_variant) (.word maximum)), .word zero),
    ("one mod maximum", wordProgram_variant
      (.binary .wordMod (.word one_variant) (.word maximum)), .word one_variant),
    ("maximum div one", wordProgram_variant
      (.binary .wordDiv (.word maximum) (.word one_variant)), .word maximum),
    ("maximum mod one", wordProgram_variant
      (.binary .wordMod (.word maximum) (.word one_variant)), .word zero),
    ("maximum div maximum", wordProgram_variant
      (.binary .wordDiv (.word maximum) (.word maximum)), .word one_variant),
    ("maximum mod maximum", wordProgram_variant
      (.binary .wordMod (.word maximum) (.word maximum)), .word zero)
  ]
  for (name, witness, expected) in cases do
    assertTrue witness.check s!"{name} failed to type-check as word"
    assertTrue (witness.run 4 == .outOfFuel)
      s!"{name} finished below the literal binary fuel boundary"
    assertTrue (witness.run 5 == .done expected)
      s!"{name} failed at the literal binary fuel boundary"

  for body in [
      Expr.binary .wordDiv .unit (.word one_variant),
      Expr.binary .wordDiv (.word one_variant) .unit,
      Expr.binary .wordMod .unit (.word one_variant),
      Expr.binary .wordMod (.word one_variant) .unit
    ] do
    assertTrue (!(wordProgram_variant body).check)
      s!"unsigned division family accepted a non-word operand: {reprStr body}"

  for body in [
      Expr.binary .wordDiv (.word seven_variant3) (.word three),
      Expr.binary .wordMod (.word seven_variant3) (.word three)
    ] do
    let wrongResult : Program := { resultType := .bool, body }
    assertTrue (!wrongResult.check)
      s!"unsigned division family was accepted with bool result: {reprStr body}"

  assertTrue
    ((wordProgram_variant (.binary .wordDiv .unit (.word one_variant))).run 5 ==
      .fault (.invalidBinaryOperands .wordDiv .unit (.word one_variant)))
    "raw wordDiv did not expose its invalid left operand"
  assertTrue
    ((wordProgram_variant (.binary .wordDiv (.word one_variant) .unit)).run 5 ==
      .fault (.invalidBinaryOperands .wordDiv (.word one_variant) .unit))
    "raw wordDiv did not expose its invalid right operand"
  assertTrue
    ((wordProgram_variant (.binary .wordMod .unit (.word one_variant))).run 5 ==
      .fault (.invalidBinaryOperands .wordMod .unit (.word one_variant)))
    "raw wordMod did not expose its invalid left operand"
  assertTrue
    ((wordProgram_variant (.binary .wordMod (.word one_variant) .unit)).run 5 ==
      .fault (.invalidBinaryOperands .wordMod (.word one_variant) .unit))
    "raw wordMod did not expose its invalid right operand"

private def testFaultOrder_variant16 : IO Unit := do
  let rightWithEffect := allocatingWritingWord_variant zero one_variant zero
  for (name, body) in [
      ("wordDiv", Expr.binary .wordDiv (.var 99) rightWithEffect),
      ("wordMod", Expr.binary .wordMod (.var 99) rightWithEffect)
    ] do
    match (wordProgram_variant body).runStateful 8 with
    | .fault (.unboundVariable 99) state =>
        assertTrue state.store.isEmpty
          s!"{name} evaluated its divisor after a numerator fault"
    | result =>
        throw (IO.userError s!"{name} exposed the wrong left fault: {reprStr result}")

  let leftWithEffect := allocatingWritingWord_variant zero one_variant seven_variant3
  for (name, body) in [
      ("wordDiv", Expr.binary .wordDiv leftWithEffect (.var 100)),
      ("wordMod", Expr.binary .wordMod leftWithEffect (.var 100))
    ] do
    match (wordProgram_variant body).runStateful 64 with
    | .fault (.unboundVariable 100) state =>
        assertTrue (state.store == [.word one_variant])
          s!"{name} divisor fault did not observe the completed numerator store"
    | result =>
        throw (IO.userError s!"{name} exposed the wrong right fault: {reprStr result}")

private def testEffectfulZeroDivisor : IO Unit := do
  let left := allocatingWritingWord_variant zero one_variant seven_variant3
  let right := allocatingWritingWord_variant zero two_variant zero
  for (name, body) in [
      ("wordDiv", Expr.binary .wordDiv left right),
      ("wordMod", Expr.binary .wordMod left right)
    ] do
    let witness := wordProgram_variant body
    assertTrue witness.check s!"effectful zero-divisor {name} failed to type-check"
    assertTrue (witness.run 28 == .outOfFuel)
      s!"effectful zero-divisor {name} finished below exact fuel"
    assertTrue
      (witness.runStateful 29 ==
        .done (.word zero) [.word one_variant, .word two_variant])
      s!"{name} did not evaluate numerator then zero divisor exactly once"

/-- Cover all named theorems plus values, types, faults, effects, and fuel. -/
def testCoreUnsignedDivision : IO Unit := do
  testValuesTypesAndLiteralFuel_variant11
  testFaultOrder_variant16
  testEffectfulZeroDivisor

end Tests
end
