import Solcore.Core.Check
import Solcore.Core.BoundedSafety
import Solcore.Core.HostRunner

/-! Native Integer cases cover mathematical range, signs, primitive typing,
shared cells, genuine checkpoints, and the existing Word-only host boundary. -/

set_option autoImplicit false

namespace Tests.CoreIntegers

open Solcore.Core

private def huge : Int := Int.ofNat (2 ^ 300)

private def arithmetic (op : BinaryOp) (left right : Int) : Program := {
  resultType := op.resultType
  body := .binary op (.integer left) (.integer right)
}

private def unary (op : UnaryOp) (value : Expr) : Program := {
  resultType := op.resultType
  body := .unary op value
}

example (left right : Int) : Evaluates [] []
    (.binary .integerDiv (.integer left) (.integer right))
    (.integer (Integer.divide left right)) [] :=
  .binary .integer .integer rfl

example (left right : Int) : Evaluates [] []
    (.binary .integerMod (.integer left) (.integer right))
    (.integer (Integer.modulo left right)) [] :=
  .binary .integer .integer rfl

example (value : Int) : Evaluates [] []
    (.unary .integerToWord (.integer value)) (.word (Word.ofIntModulo value)) [] :=
  .unary .integer rfl

private def effects : Program := {
  resultType := .integer
  body := .letE (.newCell .integer (.integer 1))
    (.binary .integerSub
      (.letE (.storeCell (.var 0) (.integer 7)) (.loadCell (.var 1)))
      (.letE (.storeCell (.var 0) (.integer 10)) (.loadCell (.var 1))))
}

private theorem effects_checked : effects.check = true := rfl
private theorem effects_run : effects.runStateful 64 = .done (.integer (-3)) [.integer 10] := rfl

/-- The executable CEK trace supplies a genuine finite evaluation witness. -/
example : Evaluates [] [] effects.body (.integer (-3)) [.integer 10] :=
  runStateful_evaluation_sound effects_run

example (fuel : Nat) : (effects.runStateful fuel).HasType .integer :=
  effects.checked_runStateful_has_type effects_checked fuel

example (fuel additional : Nat) (checkpoint : State)
    (suspended : effects.runStateful fuel = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType .integer ∧
      runStateful additional checkpoint = effects.runStateful (fuel + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound effects_checked).bodyHasType)
    suspended additional

private def capture : Program := {
  resultType := .integer
  body := .letE (.newCell .integer (.integer 4))
    (.letE (.lambda .integer .integer
      (.letE (.storeCell (.var 1) (.binary .integerAdd (.loadCell (.var 1)) (.var 0)))
        (.loadCell (.var 2))))
      (.letE (.apply (.var 0) (.integer 3)) (.apply (.var 1) (.integer 5))))
}

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def assertProgram (program : Program) (value : Value) (store : Store := []) : IO Unit := do
  assertTrue program.check "native Integer program did not type-check"
  assertTrue (program.runStateful 1000 == .done value store)
    s!"native Integer runner returned {reprStr (program.runStateful 1000)}"

def run : IO Unit := do
  assertProgram { resultType := .integer, body := .integer (-huge) } (.integer (-huge))
  assertProgram (arithmetic .integerAdd huge huge) (.integer (2 * huge))
  assertProgram (arithmetic .integerSub (-huge) 17) (.integer (-huge - 17))
  assertProgram (arithmetic .integerMul huge (-huge)) (.integer (-(huge * huge)))
  for left in [-huge - 7, -7, 0, 7, huge + 7] do
    for right in [-3, -1, 0, 1, 3] do
      assertProgram (arithmetic .integerDiv left right)
        (.integer (if right = 0 then 0 else left / right))
      assertProgram (arithmetic .integerMod left right)
        (.integer (if right = 0 then 0 else left % right))
      assertProgram (arithmetic .integerEq left right) (.bool (left == right))
      assertProgram (arithmetic .integerLt left right) (.bool (decide (left < right)))
      assertProgram (arithmetic .integerAnd left right) (.integer (Integer.bitAnd left right))
      assertProgram (arithmetic .integerOr left right) (.integer (Integer.bitOr left right))
      assertProgram (arithmetic .integerXor left right) (.integer (Integer.bitXor left right))
    assertProgram (unary .integerNot (.integer left)) (.integer (~~~left))
    assertProgram (unary .integerToWord (.integer left)) (.word (Word.ofIntModulo left))
  assertProgram (arithmetic .integerAnd (-1) huge) (.integer huge)
  assertProgram (arithmetic .integerOr (-1) huge) (.integer (-1))
  assertProgram (arithmetic .integerXor (-1) huge) (.integer (~~~huge))
  let maxWord := Word.ofNatModulo (wordModulus - 1)
  assertProgram (unary .wordToInteger (.word maxWord)) (.integer (Int.ofNat maxWord.val))

  assertProgram effects (.integer (-3)) [.integer 10]
  assertProgram capture (.integer 12) [.integer 12]
  assertTrue (effects.runHostStateful 100 == .done (.integer (-3)) [.integer 10])
    "native Integer pure execution must have the same host-runner outcome"
  match effects.runStateful 6 with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 100 checkpoint == effects.runStateful 106)
        "Integer cell effects must resume from the genuine checkpoint"
  | other => throw (IO.userError s!"expected Integer suspension, got {reprStr other}")

  let bad : Program := {
    resultType := .integer
    body := .binary .integerAdd (.integer 1) (.word Word.zero) }
  assertTrue (!bad.check) "integer primitives must reject Word operands"
  assertTrue (!(unary .wordToInteger (.integer 1)).check)
    "wordToInteger must require a Word"
  assertTrue (!(unary .integerToWord (.word Word.zero)).check)
    "integerToWord must require an Integer"
  assertTrue (!( { resultType := .integer, body := .bool true } : Program).check)
    "Integer result annotation must be checked"
  let hostBad : Program := { resultType := .word, body := .apply (.var 0) (.integer 0) }
  assertTrue (!hostBad.checkHost) "storageRead retains its Word parameter ABI"
  let hostConverted : Program := {
    resultType := .word
    body := .apply (.var 0) (.unary .integerToWord (.integer (-1))) }
  assertTrue hostConverted.checkHost "Integer may reach Word host functions through explicit conversion"
  match hostConverted.runHostStateful 20 with
  | .suspended suspension _ =>
      assertTrue (suspension.request == .storageRead (Word.ofIntModulo (-1)))
        "host request must contain the converted Word"
  | other => throw (IO.userError s!"expected converted Word host request, got {reprStr other}")

end Tests.CoreIntegers
