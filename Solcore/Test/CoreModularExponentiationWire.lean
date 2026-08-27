import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire rejection regressions for the internal-only `wordPow` operator. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep base-left/exponent-right `wordPow` outside both frozen Core wires. -/
def testCoreModularExponentiationWire : IO Unit := do
  let base := Word.ofNatModulo 2
  let exponent := Word.ofNatModulo 8
  let expression : Expr := .binary .wordPow (.word base) (.word exponent)
  let handwritten : Expr :=
    Expr.binary .wordPow (Expr.word base) (Expr.word exponent)

  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    "Core wire v1 must reject wordPow"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? handwritten).isNone
    "Core wire v1 must reject handwritten wordPow"
  assertTrue
    (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordPow).isNone
    "Core wire v2 must not publish a wordPow operator tag"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
    "Core wire v2 must reject wordPow"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    "Core wire v2 must reject handwritten wordPow"

end Tests
