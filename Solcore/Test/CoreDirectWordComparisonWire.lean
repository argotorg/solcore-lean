import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for the existing direct word comparisons. -/

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
    s!"Core wire v2 did not preserve the {name} tag and operand order"
  assertTrue
    (projected == Solcore.Core.Wire.V2.Expr.ofCore? handwritten)
    s!"{name} did not exactly match its handwritten Core expression"

  match projected with
  | none =>
      throw (IO.userError s!"{name} unexpectedly lacked a v2 projection")
  | some wireExpression =>
      assertTrue (wireExpression.toCore == expression)
        s!"{name} did not round-trip through Core wire v2"
      match Solcore.Core.Wire.V2.decodeExpr
          (Solcore.Core.Wire.V2.encodeExpr wireExpression) with
      | .ok decoded =>
          assertTrue (decoded == wireExpression)
            s!"{name} changed during its v2 JSON round-trip"
      | .error _ =>
          throw (IO.userError s!"{name} v2 JSON failed to decode")

/-- Cover v1 rejection and exact v2 left/right projection for comparisons. -/
def testCoreDirectWordComparisonWire : IO Unit := do
  let left : Word := ⟨wordModulus - 1, by decide⟩
  let right : Word := ⟨1, by decide⟩

  for (name, op, wireOp) in [
      ("wordEq", BinaryOp.wordEq, Solcore.Core.Wire.V2.BinaryOp.wordEq),
      ("wordGt", BinaryOp.wordGt, Solcore.Core.Wire.V2.BinaryOp.wordGt)
    ] do
    let expression : Expr := .binary op (.word left) (.word right)
    let handwritten : Expr :=
      Expr.binary op (Expr.word left) (Expr.word right)
    let expected : Solcore.Core.Wire.V2.Expr :=
      .binary wireOp (.word left) (.word right)
    testProjection name expression handwritten expected

end Tests
