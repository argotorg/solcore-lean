import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for the existing logical shift operators. -/

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
    s!"Core wire v2 did not preserve the {name} tag and value/shift order"
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

/-- Cover v1 rejection and exact v2 value-left/shift-right projection. -/
def testCoreLogicalShiftWire : IO Unit := do
  let value : Word := ⟨8, by decide⟩
  let shift : Word := ⟨3, by decide⟩

  let shiftLeft : Expr := .binary .wordShl (.word value) (.word shift)
  let handwrittenLeft : Expr :=
    Expr.binary .wordShl (Expr.word value) (Expr.word shift)
  let expectedLeft : Solcore.Core.Wire.V2.Expr :=
    .binary .wordShl (.word value) (.word shift)
  testProjection "wordShl" shiftLeft handwrittenLeft expectedLeft

  let shiftRight : Expr := .binary .wordShr (.word value) (.word shift)
  let handwrittenRight : Expr :=
    Expr.binary .wordShr (Expr.word value) (Expr.word shift)
  let expectedRight : Solcore.Core.Wire.V2.Expr :=
    .binary .wordShr (.word value) (.word shift)
  testProjection "wordShr" shiftRight handwrittenRight expectedRight

end Tests
