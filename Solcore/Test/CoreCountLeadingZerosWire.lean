import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire rejection regressions for the internal-only `wordClz` operator. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep `wordClz` outside both frozen Core wire versions. -/
def testCoreCountLeadingZerosWire : IO Unit := do
  let operand := Word.ofNatModulo 7
  let expression : Expr := .unary .wordClz (.word operand)
  let handwritten : Expr := Expr.unary .wordClz (Expr.word operand)

  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    "Core wire v1 must reject wordClz"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? handwritten).isNone
    "Core wire v1 must reject handwritten wordClz"
  assertTrue
    (Solcore.Core.Wire.V2.UnaryOp.ofCore? .wordClz).isNone
    "Core wire v2 must not publish a wordClz operator tag"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
    "Core wire v2 must reject wordClz"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    "Core wire v2 must reject handwritten wordClz"

end Tests
