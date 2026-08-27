import Solcore.Core.Primitive
import Solcore.Core.Wire
import Solcore.Core.Wire.V2

/-! Frozen-wire rejection for the internal ternary modular operators. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def testRejection (name : String) (operation : TernaryOp) : IO Unit := do
  let first := Word.ofNatModulo 7
  let second := Word.ofNatModulo 3
  let modulus := Word.ofNatModulo 5
  let expression : Expr :=
    .ternary operation (.word first) (.word second) (.word modulus)
  let handwritten : Expr :=
    Expr.ternary operation (Expr.word first) (Expr.word second)
      (Expr.word modulus)

  assertTrue (expression == handwritten)
    s!"{name} shorthand changed its Core structure"
  match expression with
  | .ternary actualOperation (.word actualFirst) (.word actualSecond)
      (.word actualModulus) =>
      assertTrue
        (actualOperation == operation && actualFirst == first &&
          actualSecond == second && actualModulus == modulus)
        s!"{name} changed first/second/modulus operand order"
  | _ => throw (IO.userError s!"{name} lost its ternary Core structure")

  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? expression).isNone
    s!"Core wire v1 must reject {name}"
  assertTrue (Solcore.Core.Wire.V1.Expr.ofCore? handwritten).isNone
    s!"Core wire v1 must reject handwritten {name}"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? expression).isNone
    s!"Core wire v2 must reject {name}"
  assertTrue (Solcore.Core.Wire.V2.Expr.ofCore? handwritten).isNone
    s!"Core wire v2 must reject handwritten {name}"

/-- Both ternary operations remain internal and retain their operand order. -/
def testCoreTernaryModularArithmeticWire : IO Unit := do
  for (name, operation) in
      [ ("wordAddMod", TernaryOp.wordAddMod)
      , ("wordMulMod", TernaryOp.wordMulMod) ] do
    testRejection name operation

end Tests
