import Solcore.Core.Derived
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for the internal derived signed less-than builder. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep `wordSlt` and its exact expansion outside both frozen Core wires. -/
def testCoreDerivedSignedComparisonWire : IO Unit := do
  let left : Expr := .word (Word.ofNatModulo 7)
  let right : Expr := .var 0
  let derived := left.wordSlt right
  let handwritten : Expr :=
    .letE left
      (.letE (right.weakenAt 0)
        (.binary .wordSgt (.var 0) (.var 1)))

  assertTrue (derived == handwritten)
    "wordSlt must use the exact effect-safe nested-let expansion"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? derived).isNone
    "Core wire v1 must reject derived wordSlt"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? handwritten).isNone
    "Core wire v1 must reject handwritten wordSlt expansion"
  assertTrue
    (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordSgt).isNone
    "Core wire v2 must not publish the underlying wordSgt tag"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? derived).isNone
    "Core wire v2 must reject derived wordSlt"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    "Core wire v2 must reject handwritten wordSlt expansion"

end Tests
