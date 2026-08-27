import Solcore.Core.DerivedComparisons
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for derived boolean-valued word comparisons. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def testProjection
    (name : String) (builder handwritten : Expr) : IO Unit := do
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? builder).isNone
    s!"Core wire v1 must reject the primitive expansion required by {name}"
  let projected := Solcore.Core.Wire.V2.Expr.ofCore? builder
  assertTrue projected.isSome
    s!"Core wire v2 must project {name} through its existing expression forms"
  assertTrue
    (projected == Solcore.Core.Wire.V2.Expr.ofCore? handwritten)
    s!"{name} must project exactly like its ADR-0030 handwritten expansion"
  match projected with
  | none =>
      throw (IO.userError s!"{name} unexpectedly lacked a v2 projection")
  | some wireExpression =>
      assertTrue (wireExpression.toCore == builder)
        s!"{name} must round-trip through the ordinary v2 expression tree"

/-- Cover exact v1 rejection and v2 expansion projection for every ADR-0030
derived comparison builder. -/
def testCoreDerivedComparisonWire : IO Unit := do
  let left : Expr := .word Word.maximum
  let right : Expr := .word Word.zero

  let wordNe := left.wordNe right
  let wordNeExpansion : Expr :=
    .unary .boolNot (.binary .wordEq left right)
  testProjection "wordNe" wordNe wordNeExpansion

  let wordLt := left.wordLt right
  let wordLtExpansion : Expr :=
    .letE left
      (.letE (right.weakenAt 0)
        (.binary .wordGt (.var 0) (.var 1)))
  testProjection "wordLt" wordLt wordLtExpansion

  let wordLe := left.wordLe right
  let wordLeExpansion : Expr :=
    .unary .boolNot (.binary .wordGt left right)
  testProjection "wordLe" wordLe wordLeExpansion

  let wordGe := left.wordGe right
  let wordGeExpansion : Expr :=
    .unary .boolNot
      (.letE left
        (.letE (right.weakenAt 0)
          (.binary .wordGt (.var 0) (.var 1))))
  testProjection "wordGe" wordGe wordGeExpansion

end Tests
