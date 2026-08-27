import Solcore.Core.DerivedSignedNonStrictComparisons
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for derived signed non-strict comparisons. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep signed non-strict builders and exact expansions outside frozen wires. -/
def testCoreDerivedSignedNonStrictComparisonWire : IO Unit := do
  let left : Expr := .word (Word.ofNatModulo 7)
  let right : Expr := .var 0
  let sle := left.wordSle right
  let handwrittenSle : Expr :=
    .unary .boolNot (.binary .wordSgt left right)
  let sge := left.wordSge right
  let handwrittenSge : Expr :=
    .unary .boolNot
      (.letE left
        (.letE (right.weakenAt 0)
          (.binary .wordSgt (.var 0) (.var 1))))

  assertTrue (sle == handwrittenSle)
    "wordSle must use the exact boolNot wordSgt expansion"
  assertTrue (sge == handwrittenSge)
    "wordSge must expose the weakened free-variable RHS expansion"
  for (name, expression) in
      [("wordSle", sle), ("handwritten wordSle", handwrittenSle),
       ("wordSge", sge), ("handwritten wordSge", handwrittenSge)] do
    assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
      s!"Core wire v1 must reject {name}"
    assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
      s!"Core wire v2 must reject {name}"
  assertTrue (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordSgt).isNone
    "Core wire v2 must not publish the underlying wordSgt tag"

end Tests
