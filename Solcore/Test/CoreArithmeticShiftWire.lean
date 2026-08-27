import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire rejection regressions for the internal-only `wordSar` operator. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep value-left/shift-right `wordSar` outside both frozen Core wires. -/
def testCoreArithmeticShiftWire : IO Unit := do
  let value := Word.ofNatModulo (wordModulus - 3)
  let shift := Word.ofNatModulo 1
  let expression : Expr := .binary .wordSar (.word value) (.word shift)
  let handwritten : Expr :=
    Expr.binary .wordSar (Expr.word value) (Expr.word shift)

  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    "Core wire v1 must reject wordSar"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? handwritten).isNone
    "Core wire v1 must reject handwritten wordSar"
  assertTrue
    (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordSar).isNone
    "Core wire v2 must not publish a wordSar operator tag"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
    "Core wire v2 must reject wordSar"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    "Core wire v2 must reject handwritten wordSar"

end Tests
