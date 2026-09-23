import Solcore.Core.Derived
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for internal word-valued signed comparisons. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

/-- Keep both signed flags and their canonical expansions outside frozen wires. -/
def testCoreSignedComparisonFlagWire : IO Unit := do
  let left : Expr := .word (Word.ofNatModulo 7)
  let right : Expr := .var 0
  let one : Expr := .word (Word.ofNatModulo 1)
  let zero : Expr := .word Word.zero
  let sgtFlag := left.wordSgtFlag right
  let handwrittenSgt : Expr :=
    .ifE (.binary .wordSgt left right) one zero
  let sltFlag := left.wordSltFlag right
  let handwrittenSlt : Expr :=
    .ifE
      (.letE left
        (.letE (right.weakenAt 0)
          (.binary .wordSgt (.var 0) (.var 1))))
      one zero

  assertTrue (sgtFlag == handwrittenSgt)
    "wordSgtFlag must use its canonical boolToWord expansion"
  assertTrue (sltFlag == handwrittenSlt)
    "wordSltFlag must expose the weakened free-variable RHS expansion"
  for (name, expression) in
      [("wordSgtFlag", sgtFlag), ("handwritten wordSgtFlag", handwrittenSgt),
       ("wordSltFlag", sltFlag), ("handwritten wordSltFlag", handwrittenSlt)] do
    assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
      s!"Core wire v1 must reject {name}"
    assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
      s!"Core wire v2 must reject {name}"
  assertTrue (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordSgt).isNone
    "Core wire v2 must not publish the underlying wordSgt tag"

end Tests
