import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire rejection for the internal-only `wordSignExtend` operator. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep index-left/value-right `wordSignExtend` outside both frozen wires. -/
def testCoreSignExtensionWire : IO Unit := do
  let index := Word.ofNatModulo 1
  let value := Word.ofNatModulo 0x8000
  let expression : Expr :=
    .binary .wordSignExtend (.word index) (.word value)
  let handwritten : Expr :=
    Expr.binary .wordSignExtend (Expr.word index) (Expr.word value)

  assertTrue (expression == handwritten)
    "wordSignExtend must retain index-left/value-right Core structure"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    "Core wire v1 must reject wordSignExtend"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? handwritten).isNone
    "Core wire v1 must reject handwritten wordSignExtend"
  assertTrue
    (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordSignExtend).isNone
    "Core wire v2 must not publish a wordSignExtend operator tag"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
    "Core wire v2 must reject wordSignExtend"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    "Core wire v2 must reject handwritten wordSignExtend"

end Tests
