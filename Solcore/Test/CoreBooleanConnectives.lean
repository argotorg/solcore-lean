import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.ShortCircuit
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Executable regressions for the derived short-circuit boolean connectives. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

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

private def testFrozenWireProjection : IO Unit := do
  let andExpr := Expr.boolAnd (.var 0) (.var 1)
  let andExpansion : Expr :=
    .ifE (.var 0) (.var 1) (.bool false)
  let orExpr := Expr.boolOr (.var 0) (.var 1)
  let orExpansion : Expr :=
    .ifE (.var 0) (.bool true) (.var 1)

  assertTrue
    (Solcore.Core.Wire.V1.Expr.ofCore? andExpr ==
      Solcore.Core.Wire.V1.Expr.ofCore? andExpansion)
    "boolAnd must project through v1 exactly like its handwritten expansion"
  assertTrue
    (Solcore.Core.Wire.V2.Expr.ofCore? andExpr ==
      Solcore.Core.Wire.V2.Expr.ofCore? andExpansion)
    "boolAnd must project through v2 exactly like its handwritten expansion"
  assertTrue
    (Solcore.Core.Wire.V1.Expr.ofCore? orExpr ==
      Solcore.Core.Wire.V1.Expr.ofCore? orExpansion)
    "boolOr must project through v1 exactly like its handwritten expansion"
  assertTrue
    (Solcore.Core.Wire.V2.Expr.ofCore? orExpr ==
      Solcore.Core.Wire.V2.Expr.ofCore? orExpansion)
    "boolOr must project through v2 exactly like its handwritten expansion"

/-- Cover truth tables, faults, short-circuited effects, exact fuel, weakening,
and frozen-wire projection for the derived boolean connectives. -/
def testCoreBooleanConnectives : IO Unit := do
  testTruthTables
  testTypesAndRawFaults
  testEffectsAndExactFuel
  testWeakening
  testFrozenWireProjection

end Tests
