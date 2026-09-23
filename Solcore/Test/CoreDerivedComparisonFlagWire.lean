import Solcore.Core.Derived
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire regressions for derived word-valued comparison flags. -/

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
    s!"{name} must project exactly like its ADR-0031 handwritten expansion"
  match projected with
  | none =>
      throw (IO.userError s!"{name} unexpectedly lacked a v2 projection")
  | some wireExpression =>
      assertTrue (wireExpression.toCore == builder)
        s!"{name} must round-trip through the ordinary v2 expression tree"

/-- Cover exact v1 rejection and v2 expansion projection for every ADR-0031
derived comparison flag builder. -/
def testCoreDerivedComparisonFlagWire : IO Unit := do
  let left : Expr := .var 0
  let right : Expr := .var 1
  let one : Expr := .word (Word.ofNatModulo 1)
  let zero : Expr := .word Word.zero

  let wordNeFlag := left.wordNeFlag right
  let wordNeFlagExpansion : Expr :=
    .ifE
      (.unary .boolNot (.binary .wordEq left right))
      one zero
  testProjection "wordNeFlag" wordNeFlag wordNeFlagExpansion

  let wordLtFlag := left.wordLtFlag right
  let wordLtFlagExpansion : Expr :=
    .ifE
      (.letE left
        (.letE (right.weakenAt 0)
          (.binary .wordGt (.var 0) (.var 1))))
      one zero
  testProjection "wordLtFlag" wordLtFlag wordLtFlagExpansion

  let wordLeFlag := left.wordLeFlag right
  let wordLeFlagExpansion : Expr :=
    .ifE
      (.unary .boolNot (.binary .wordGt left right))
      one zero
  testProjection "wordLeFlag" wordLeFlag wordLeFlagExpansion

  let wordGeFlag := left.wordGeFlag right
  let wordGeFlagExpansion : Expr :=
    .ifE
      (.unary .boolNot
        (.letE left
          (.letE (right.weakenAt 0)
            (.binary .wordGt (.var 0) (.var 1)))))
      one zero
  testProjection "wordGeFlag" wordGeFlag wordGeFlagExpansion

end Tests
