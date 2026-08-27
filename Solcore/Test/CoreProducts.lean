import Solcore.Core.Check
import Solcore.Core.Machine
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Executable regressions for the first internal Semantic Core vNext slice. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def assertExpectedProduct
    (name : String)
    (program : Program)
    (path : CheckPath)
    (actual : Ty) : IO Unit := do
  match program.checkDetailed with
  | .ok type =>
      throw (IO.userError s!"{name} unexpectedly checked as {reprStr type}")
  | .error error =>
      assertTrue (error.code == .expectedProduct)
        s!"{name} returned {error.codeName}, expected core.check.expected-product"
      assertTrue (error.path == path)
        s!"{name} returned path {reprStr error.path}, expected {reprStr path}"
      assertTrue (error.data == .expectedProduct actual)
        s!"{name} reported the wrong non-product type: {reprStr error.data}"

private def assertUnboundVariable
    (name : String)
    (program : Program)
    (path : CheckPath)
    (index contextSize : Nat) : IO Unit := do
  match program.checkDetailed with
  | .ok type =>
      throw (IO.userError s!"{name} unexpectedly checked as {reprStr type}")
  | .error error =>
      assertTrue (error.code == .unboundVariable)
        s!"{name} returned {error.codeName}, expected core.check.unbound-variable"
      assertTrue (error.path == path)
        s!"{name} returned path {reprStr error.path}, expected {reprStr path}"
      assertTrue (error.data == .unboundVariable index contextSize)
        s!"{name} reported the wrong variable lookup: {reprStr error.data}"

private def testProductTypingAndExecution : IO Unit := do
  let pairProgram : Program := {
    resultType := .product .bool .word
    body := .pair (.bool true) (.word Word.zero)
  }
  assertTrue pairProgram.check
    "a pair expression must infer the product of its component types"
  assertTrue (pairProgram.run 4 == .outOfFuel)
    "four transitions must be insufficient for a pair of literals"
  assertTrue (pairProgram.run 5 == .done (.pair (.bool true) (.word Word.zero)))
    "a pair of literals must finish exactly at five transitions"

  let nestedProgram : Program := {
    resultType := .product .bool (.product .unit .word)
    body := .pair (.bool false) (.pair .unit (.word Word.zero))
  }
  assertTrue nestedProgram.check
    "product types and pair values must nest recursively"
  assertTrue (nestedProgram.run 8 == .outOfFuel)
    "eight transitions must be insufficient for the nested pair witness"
  assertTrue
    (nestedProgram.run 9 ==
      .done (.pair (.bool false) (.pair .unit (.word Word.zero))))
    "the nested pair witness must finish exactly at nine transitions"

  let firstProgram : Program := {
    resultType := .bool
    body := .first (.pair (.bool true) (.word Word.zero))
  }
  assertTrue firstProgram.check
    "first must infer the left component type of a product"
  assertTrue (firstProgram.run 6 == .outOfFuel)
    "six transitions must be insufficient for first over a literal pair"
  assertTrue (firstProgram.run 7 == .done (.bool true))
    "first must finish exactly at seven transitions and select the left value"

  let secondProgram : Program := {
    resultType := .word
    body := .second (.pair (.bool true) (.word Word.zero))
  }
  assertTrue secondProgram.check
    "second must infer the right component type of a product"
  assertTrue (secondProgram.run 6 == .outOfFuel)
    "six transitions must be insufficient for second over a literal pair"
  assertTrue (secondProgram.run 7 == .done (.word Word.zero))
    "second must finish exactly at seven transitions and select the right value"

private def testProductFaultsAndOrder : IO Unit := do
  let invalidPairLeft : Program := {
    resultType := .product .unit .unit
    body := .pair (.var 11) .unit
  }
  assertUnboundVariable
    "invalid pair left" invalidPairLeft [.pairLeft] 11 0

  let invalidPairRight : Program := {
    resultType := .product .unit .unit
    body := .pair .unit (.var 22)
  }
  assertUnboundVariable
    "invalid pair right" invalidPairRight [.pairRight] 22 0

  let invalidPairBoth : Program := {
    resultType := .product .unit .unit
    body := .pair (.var 11) (.var 22)
  }
  assertUnboundVariable
    "invalid pair both" invalidPairBoth [.pairLeft] 11 0

  let invalidFirst : Program := {
    resultType := .bool
    body := .first (.bool true)
  }
  assertTrue (!invalidFirst.check)
    "first must reject a statically non-product operand"
  assertExpectedProduct "first of bool" invalidFirst [.firstOperand] .bool
  assertTrue (invalidFirst.run 2 == .fault (.expectedProduct (.bool true)))
    "the unchecked machine must fault when first receives a bool"

  let invalidSecond : Program := {
    resultType := .word
    body := .second .unit
  }
  assertTrue (!invalidSecond.check)
    "second must reject a statically non-product operand"
  assertExpectedProduct "second of unit" invalidSecond [.secondOperand] .unit
  assertTrue (invalidSecond.run 2 == .fault (.expectedProduct .unit))
    "the unchecked machine must fault when second receives unit"

  let leftFaultsFirst : Program := {
    resultType := .product .unit .unit
    body := .pair (.var 11) (.var 22)
  }
  assertTrue
    (leftFaultsFirst.run 1 == .fault (.unboundVariable 11))
    "pair construction must evaluate its left component first"

  let rightAfterLeft : Program := {
    resultType := .product .unit .unit
    body := .pair .unit (.var 22)
  }
  assertTrue
    (rightAfterLeft.run 3 == .fault (.unboundVariable 22))
    "pair construction must evaluate the right component after the left finishes"

private def testFrozenProductWireBoundary : IO Unit := do
  let productType : Ty := .product .bool (.product .unit .word)
  let pairValue : Value := .pair (.bool true) (.pair .unit (.word Word.zero))
  let pairExpr : Expr := .pair (.bool true) (.word Word.zero)
  let firstExpr : Expr := .first pairExpr
  let secondExpr : Expr := .second pairExpr

  assertTrue (Solcore.Core.Wire.V1.Ty.ofCore? productType).isNone
    "Semantic Core v1 must reject product types"
  assertTrue (Solcore.Core.Wire.V2.Ty.ofCore? productType).isNone
    "Semantic Core v2 must reject product types"
  assertTrue (Solcore.Core.Wire.V1.Value.ofCore? pairValue).isNone
    "Semantic Core v1 must reject pair values"
  assertTrue (Solcore.Core.Wire.V2.Value.ofCore? pairValue).isNone
    "Semantic Core v2 must reject pair values"

  for expression in [pairExpr, firstExpr, secondExpr] do
    assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
      s!"Semantic Core v1 encoded an internal product expression: {reprStr expression}"
    assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
      s!"Semantic Core v2 encoded an internal product expression: {reprStr expression}"

  let nestedInV1Shape : Expr := .letE .unit (.pair (.var 0) .unit)
  let nestedInV2Shape : Expr := .unary .boolNot (.first (.pair (.bool true) .unit))
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? nestedInV1Shape).isNone
    "Semantic Core v1 must reject a pair nested under an old expression"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? nestedInV2Shape).isNone
    "Semantic Core v2 must reject a projection nested under an old expression"

  let productResultProgram : Program := {
    resultType := productType
    body := .pair (.bool true) (.pair .unit (.word Word.zero))
  }
  assertTrue (Solcore.Core.Wire.V1.Program.ofCore? productResultProgram).isNone
    "Semantic Core v1 must reject programs with product result types"
  assertTrue (Solcore.Core.Wire.V2.Program.ofCore? productResultProgram).isNone
    "Semantic Core v2 must reject programs with product result types"

  let oldResultProgram : Program := {
    resultType := .bool
    body := .first (.pair (.bool true) .unit)
  }
  assertTrue (Solcore.Core.Wire.V1.Program.ofCore? oldResultProgram).isNone
    "Semantic Core v1 must reject product expressions under an old result type"
  assertTrue (Solcore.Core.Wire.V2.Program.ofCore? oldResultProgram).isNone
    "Semantic Core v2 must reject product expressions under an old result type"

/-- Cover product typing, execution order, projection faults, and frozen-wire
isolation as one focused semantic-slice regression. -/
def testCoreProducts : IO Unit := do
  testProductTypingAndExecution
  testProductFaultsAndOrder
  testFrozenProductWireBoundary

end Tests
