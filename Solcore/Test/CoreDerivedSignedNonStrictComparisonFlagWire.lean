import Solcore.Core.Derived
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for signed non-strict word-valued comparisons. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

/-- Fix the exact expansions, including the weakened free-variable RHS of Sge. -/
def testCoreDerivedSignedNonStrictComparisonFlagWire : IO Unit := do
  let left : Expr := .word (Word.ofNatModulo 7)
  let right : Expr := .var 0
  let one : Expr := .word (Word.ofNatModulo 1)
  let zero : Expr := .word Word.zero
  let sleFlag := left.wordSleFlag right
  let handwrittenSle : Expr :=
    .ifE (.unary .boolNot (.binary .wordSgt left right)) one zero
  let sgeFlag := left.wordSgeFlag right
  let handwrittenSge : Expr :=
    .ifE
      (.unary .boolNot
        (.letE left
          (.letE (right.weakenAt 0)
            (.binary .wordSgt (.var 0) (.var 1)))))
      one zero

  assertTrue (sleFlag == handwrittenSle)
    "wordSleFlag must equal its complete boolToWord expansion"
  assertTrue (sgeFlag == handwrittenSge)
    "wordSgeFlag must retain source order and weakened free-variable structure"
  for (name, expression) in
      [("wordSleFlag", sleFlag), ("handwritten wordSleFlag", handwrittenSle),
       ("wordSgeFlag", sgeFlag), ("handwritten wordSgeFlag", handwrittenSge)] do
    assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
      s!"Core wire v1 must reject {name}"
    assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
      s!"Core wire v2 must reject {name}"
  assertTrue (Solcore.Core.Wire.V2.BinaryOp.ofCore? .wordSgt).isNone
    "Core wire v2 must not publish the underlying wordSgt tag"

end Tests
