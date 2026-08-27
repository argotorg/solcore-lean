import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for unsigned division and remainder. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def one : Word :=
  ⟨1, by decide⟩

private def testProjection
    (name : String)
    (expression handwritten : Expr)
    (expected : Solcore.Core.Wire.V2.Expr) : IO Unit := do
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    s!"Core wire v1 must reject the {name} primitive expression"

  let projected := Solcore.Core.Wire.V2.Expr.ofCore? expression
  assertTrue (projected == some expected)
    s!"Core wire v2 did not preserve the {name} operator and operand order"
  assertTrue
    (projected == Solcore.Core.Wire.V2.Expr.ofCore? handwritten)
    s!"{name} did not exactly match its handwritten Core expression"

  match projected with
  | none =>
      throw (IO.userError s!"{name} unexpectedly lacked a v2 projection")
  | some wireExpression =>
      assertTrue (wireExpression.toCore == expression)
        s!"{name} did not round-trip through Core wire v2"

/-- Cover v1 rejection and exact v2 projection for both unsigned operations. -/
def testCoreUnsignedDivisionWire : IO Unit := do
  let division : Expr := .binary .wordDiv (.word one) (.word Word.zero)
  let handwrittenDivision : Expr :=
    Expr.binary .wordDiv (Expr.word one) (Expr.word Word.zero)
  let expectedDivision : Solcore.Core.Wire.V2.Expr :=
    .binary .wordDiv (.word one) (.word Word.zero)
  testProjection "wordDiv" division handwrittenDivision expectedDivision

  let remainder : Expr := .binary .wordMod (.word Word.zero) (.word one)
  let handwrittenRemainder : Expr :=
    Expr.binary .wordMod (Expr.word Word.zero) (Expr.word one)
  let expectedRemainder : Solcore.Core.Wire.V2.Expr :=
    .binary .wordMod (.word Word.zero) (.word one)
  testProjection "wordMod" remainder handwrittenRemainder expectedRemainder

end Tests
