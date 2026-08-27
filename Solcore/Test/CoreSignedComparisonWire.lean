import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire rejection regressions for the internal-only `wordSgt` operator. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep boolean signed word comparison outside both frozen Core wires. -/
def testCoreSignedComparisonWire : IO Unit := do
  let left := Word.ofNatModulo 1
  let right := Word.maximum
  let expression : Expr := .binary .wordSgt (.word left) (.word right)
  let handwritten : Expr :=
    Expr.binary .wordSgt (Expr.word left) (Expr.word right)

  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    "Core wire v1 must reject wordSgt"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? handwritten).isNone
    "Core wire v1 must reject handwritten wordSgt"
  assertTrue
    (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordSgt).isNone
    "Core wire v2 must not publish a wordSgt operator tag"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
    "Core wire v2 must reject wordSgt"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    "Core wire v2 must reject handwritten wordSgt"

end Tests
