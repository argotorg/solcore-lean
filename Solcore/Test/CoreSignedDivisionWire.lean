import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire rejection for the internal signed division and modulo operators. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def testRejection (name : String) (operation : BinaryOp) : IO Unit := do
  let dividend := Word.ofNatModulo 0x80
  let divisor := Word.ofNatModulo 3
  let expression : Expr :=
    .binary operation (.word dividend) (.word divisor)
  let handwritten : Expr :=
    Expr.binary operation (Expr.word dividend) (Expr.word divisor)

  assertTrue (expression == handwritten)
    s!"{name} must retain dividend-left/divisor-right Core structure"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    s!"Core wire v1 must reject {name}"
  assertTrue (Solcore.Core.Wire.V2.BinaryOp.ofCore? operation).isNone
    s!"Core wire v2 must not publish a {name} operator tag"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
    s!"Core wire v2 must reject {name}"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    s!"Core wire v2 must reject handwritten {name}"

/-- Both signed operations remain internal to Core and preserve operand order. -/
def testCoreSignedDivisionWire : IO Unit := do
  for (name, operation) in
      [ ("wordSdiv", BinaryOp.wordSdiv)
      , ("wordSmod", BinaryOp.wordSmod) ] do
    testRejection name operation

end Tests
