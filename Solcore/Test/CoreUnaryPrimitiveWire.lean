import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for the two existing unary primitives. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def testProjection
    (name : String)
    (expression handwritten : Expr)
    (expected : Solcore.Core.Wire.V2.Expr) : IO Unit := do
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    s!"Core wire v1 must reject the {name} primitive expression"

  let projected := Solcore.Core.Wire.V2.Expr.ofCore? expression
  assertTrue (projected == some expected)
    s!"Core wire v2 did not preserve the {name} operator and operand"
  assertTrue
    (projected == Solcore.Core.Wire.V2.Expr.ofCore? handwritten)
    s!"{name} did not exactly match its handwritten Core expression"

  match projected with
  | none =>
      throw (IO.userError s!"{name} unexpectedly lacked a v2 projection")
  | some wireExpression =>
      assertTrue (wireExpression.toCore == expression)
        s!"{name} did not round-trip through Core wire v2"

/-- Cover v1 rejection and exact v2 projection for both unary operator tags. -/
def testCoreUnaryPrimitiveWire : IO Unit := do
  let boolExpression : Expr := .unary .boolNot (.bool true)
  let handwrittenBool : Expr := Expr.unary .boolNot (Expr.bool true)
  let expectedBool : Solcore.Core.Wire.V2.Expr :=
    .unary .boolNot (.bool true)
  testProjection "boolNot" boolExpression handwrittenBool expectedBool

  let wordExpression : Expr := .unary .wordNot (.word Word.zero)
  let handwrittenWord : Expr := Expr.unary .wordNot (Expr.word Word.zero)
  let expectedWord : Solcore.Core.Wire.V2.Expr :=
    .unary .wordNot (.word Word.zero)
  testProjection "wordNot" wordExpression handwrittenWord expectedWord

end Tests
