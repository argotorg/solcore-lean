import Solcore.Frontend.RustYulPrimitives
import Solcore.Core.Machine

set_option autoImplicit false

namespace Tests.RustYulPrimitives

open Solcore.Core
open Solcore.Frontend.RustYulPrimitives

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def lower (name : String) (arguments : List Expr) : IO Lowered :=
  match compile name arguments with
  | .ok lowered => pure lowered
  | .error error => throw (IO.userError s!"Yul {name}: {reprStr error}")

private def word (value : Int) : Word := Word.ofIntModulo value
private def literal (value : Int) : Expr := .word (word value)

private def fails (name : String) (arguments : List Expr) (expected : Error) : Bool :=
  match compile name arguments with
  | .error error => error == expected
  | .ok _ => false

private def checkWord (name : String) (arguments : List Int) (expected : Int) : IO Unit := do
  let lowered ← lower name (arguments.map literal)
  let program : Program := ⟨lowered.type, lowered.expression, []⟩
  require program.check s!"Yul {name}: invalid generated Core type"
  require (program.run 500 == .done (.word (word expected)))
    s!"Yul {name}{reprStr arguments}: expected {expected}, got {reprStr (program.run 500)}"

private def tick : Expr :=
  .letE (.loadCell (.var 0))
    (.letE (.storeCell (.var 1) (.binary .wordAdd (.var 0) (literal 1))) (.var 1))

def run : IO Unit := do
  let maximum : Int := 2 ^ 256 - 1
  let minimum : Int := -(2 ^ 255)
  for (name, arguments, expected) in [
      ("add", [maximum, 1], 0), ("sub", [7, 11], -4), ("mul", [7, 9], 63),
      ("div", [17, 5], 3), ("div", [17, 0], 0),
      ("mod", [17, 5], 2), ("mod", [17, 0], 0),
      ("sdiv", [-7, 2], -3), ("sdiv", [minimum, -1], minimum), ("sdiv", [-7, 0], 0),
      ("smod", [-7, 2], -1), ("smod", [7, -2], 1), ("smod", [-7, 0], 0),
      ("exp", [2, 256], 0), ("exp", [0, 0], 1),
      ("signextend", [0, 128], -128), ("signextend", [32, 128], 128),
      ("lt", [1, 2], 1), ("lt", [2, 1], 0), ("lt", [-1, 0], 0),
      ("gt", [2, 1], 1), ("gt", [2, 2], 0),
      ("slt", [-1, 0], 1), ("slt", [0, -1], 0),
      ("sgt", [0, -1], 1), ("sgt", [-1, 0], 0),
      ("eq", [5, 5], 1), ("eq", [5, 6], 0),
      ("iszero", [0], 1), ("iszero", [256], 0),
      ("and", [12, 10], 8), ("or", [12, 10], 14), ("xor", [12, 10], 6),
      ("not", [0], -1), ("byte", [0, 171 * 2 ^ 248], 171), ("byte", [32, -1], 0),
      ("shl", [3, 5], 40), ("shl", [256, 1], 0),
      ("shr", [3, 40], 5), ("shr", [256, -1], 0),
      ("sar", [1, -3], -2), ("sar", [256, -1], -1),
      ("clz", [0], 256), ("clz", [1], 255), ("clz", [2 ^ 255], 0),
      ("addmod", [maximum, 1, 3], 1), ("addmod", [1, 2, 0], 0),
      ("mulmod", [2 ^ 255, 2, 3], 1), ("mulmod", [1, 2, 0], 0)] do
    checkWord name arguments expected

  let popped ← lower "pop" [literal 7]
  let popProgram : Program := ⟨popped.type, popped.expression, []⟩
  require (popProgram.check && popProgram.run 100 == .done .unit)
    "Yul pop did not consume a word and return unit"
  let invalidPop ← lower "pop" [.bool true]
  require (!(Program.mk invalidPop.type invalidPop.expression []).check)
    "Yul pop silently accepted a Boolean argument"
  let invalidAdd ← lower "add" [.bool true, literal 1]
  require (!(Program.mk invalidAdd.type invalidAdd.expression []).check)
    "Yul add silently accepted a Boolean argument"
  require (fails "add" [literal 1] (.wrongArity "add" 2 1))
    "Yul add accepted missing arguments"
  require (fails "clz" [literal 1, literal 2] (.wrongArity "clz" 1 2))
    "Yul clz accepted extra arguments"
  for name in ["sload", "mstore", "keccak256", "return", "call", "missing"] do
    require (!supports name && fails name [] (.unknownBuiltin name))
      s!"Yul pure lowering silently accepted effect {name}"

  let ordered ← lower "sub" [tick, tick]
  let orderedProgram : Program := {
    resultType := .product .word .word
    body := .letE (.newCell .word (literal 0))
      (.pair ordered.expression (.loadCell (.var 0)))
  }
  require orderedProgram.check "effectful Yul argument lowering is ill-typed"
  let orderedExpected : StatefulRunResult :=
    .done (.pair (.word (word 1)) (.word (word 2))) [.word (word 2)]
  require (orderedProgram.runStateful 500 == orderedExpected)
    "Yul arguments were not evaluated once each, right to left"
  match orderedProgram.runStateful 10 with
  | .outOfFuel state =>
      require (runStateful 500 state == orderedExpected)
        "resuming a Yul argument computation repeated or lost an effect"
  | _ => throw (IO.userError "Yul resumption fixture did not suspend")

  let ternary ← lower "addmod" [tick, tick, tick]
  let ternaryProgram : Program := {
    resultType := .product .word .word
    body := .letE (.newCell .word (literal 5))
      (.pair ternary.expression (.loadCell (.var 0)))
  }
  require (ternaryProgram.check && ternaryProgram.runStateful 500 ==
      .done (.pair (.word (word 3)) (.word (word 8))) [.word (word 8)])
    "Yul ternary argument positions or right-to-left effects changed"

  let discarded ← lower "pop" [tick]
  let discardedProgram : Program := {
    resultType := .product .unit .word
    body := .letE (.newCell .word (literal 0))
      (.pair discarded.expression (.loadCell (.var 0)))
  }
  require (discardedProgram.check && discardedProgram.run 500 ==
      .done (.pair .unit (.word (word 1))))
    "Yul pop discarded the argument's effects"

  let firstFault ← lower "sub" [.var 98, .var 99]
  require ((Program.mk firstFault.type firstFault.expression []).run 100 ==
      .fault (.unboundVariable 99))
    "Yul evaluated the left argument before a failing right argument"

end Tests.RustYulPrimitives
