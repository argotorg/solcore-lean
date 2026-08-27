import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire rejection regressions for the internal-only `wordByte` operator. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep index-left/value-right `wordByte` outside both frozen Core wires. -/
def testCoreByteSelectionWire : IO Unit := do
  let index : Word := ⟨30, by decide⟩
  let value : Word := ⟨0x1122, by decide⟩
  let expression : Expr := .binary .wordByte (.word index) (.word value)
  let handwritten : Expr :=
    Expr.binary .wordByte (Expr.word index) (Expr.word value)

  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    "Core wire v1 must reject wordByte"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? handwritten).isNone
    "Core wire v1 must reject handwritten wordByte"
  assertTrue
    (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordByte).isNone
    "Core wire v2 must not publish a wordByte operator tag"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
    "Core wire v2 must reject wordByte"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    "Core wire v2 must reject handwritten wordByte"

end Tests
