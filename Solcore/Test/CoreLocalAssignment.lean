import Solcore.Core.LocalAssignment
import Solcore.Core.FuelResumptionProperties

/-! Concrete shared-store tests distinguish the selected snapshot from a value
written by the RHS, and preserve RHS effects on both language-failure paths. -/

set_option autoImplicit false

namespace Tests.CoreLocalAssignment

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def present (value : Value) : Value := .inRight .unit value
private def invalidReason : Word := word 63
private def rhsReason : Word := word 64

/-- Outer scope is the target reference, then the trace reference. -/
private def target : Expr :=
  .letE (.storeCell (.var 1) (.inRight .unit (literal 9))) (.var 1)

private def rhs (failure : Bool) : Expr :=
  .letE (.storeCell (.var 0) (.inRight .unit (literal 100)))
    (if failure then LanguageResult.failure .word (.word rhsReason)
     else LanguageResult.success (literal 3))

private def next : Expr :=
  .letE (.storeCell (.var 1) (.inRight .unit (literal 888)))
    (OptionalCell.read .word (.var 1) invalidReason)

private def withCells (absent : Bool) (body : Expr) : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (OptionalCell.allocateInitialized .word (literal 1))
    (.letE (if absent then OptionalCell.allocate .word
      else OptionalCell.allocateInitialized .word (literal 2)) body)
}

private def compoundProgram (operator : LocalAssignment.Operator) (absent failure : Bool) : Program :=
  withCells absent (LocalAssignment.compound .word operator target (rhs failure) next invalidReason)

private def unaryProgram (absent : Bool) : Program :=
  withCells absent (LocalAssignment.bitNot .word target next invalidReason)

private theorem snapshot_checked : (compoundProgram .add false false).check = true := by
  simp [compoundProgram, withCells, target, rhs, next, LocalAssignment.compound,
    LocalAssignment.Operator.core, LocalAssignment.weakenFive, LocalAssignment.weakenThree,
    LocalAssignment.weakenTwo, OptionalCell.allocateInitialized,
    OptionalCell.read, OptionalCell.cellType, LanguageResult.bind, LanguageResult.failure,
    LanguageResult.success, literal, Expr.weakenAt]
  decide

set_option maxRecDepth 4096 in
/-- `2 += RHS` uses two even though RHS writes one hundred to the same cell. -/
private theorem snapshot_completed : (compoundProgram .add false false).runStateful 250 =
    .done (.inRight .word (scalar 5)) [present (scalar 888), present (scalar 5)] := by
  simp [compoundProgram, withCells, target, rhs, next, LocalAssignment.compound,
    LocalAssignment.Operator.core, LocalAssignment.weakenFive, LocalAssignment.weakenThree,
    LocalAssignment.weakenTwo, OptionalCell.allocateInitialized,
    OptionalCell.read, OptionalCell.cellType, LanguageResult.bind, LanguageResult.failure,
    LanguageResult.success, literal, Expr.weakenAt]
  rfl

set_option maxRecDepth 4096 in
/-- An absent snapshot remains invalid after a successful RHS initializes it. -/
private theorem absence_completed : (compoundProgram .add true false).runStateful 250 =
    .done (.inLeft .word (.word invalidReason)) [present (scalar 9), present (scalar 100)] := by
  simp [compoundProgram, withCells, target, rhs, next, LocalAssignment.compound,
    LocalAssignment.Operator.core, LocalAssignment.weakenFive, LocalAssignment.weakenThree,
    LocalAssignment.weakenTwo, OptionalCell.allocateInitialized, OptionalCell.allocate,
    OptionalCell.read, OptionalCell.cellType, LanguageResult.bind, LanguageResult.failure,
    LanguageResult.success, literal, Expr.weakenAt]
  rfl

set_option maxRecDepth 4096 in
/-- The RHS reason wins over the absent snapshot and retains the RHS write. -/
private theorem rhs_failure_completed : (compoundProgram .add true true).runStateful 250 =
    .done (.inLeft .word (.word rhsReason)) [present (scalar 9), present (scalar 100)] := by
  simp [compoundProgram, withCells, target, rhs, next, LocalAssignment.compound,
    LocalAssignment.Operator.core, LocalAssignment.weakenFive, LocalAssignment.weakenThree,
    LocalAssignment.weakenTwo, OptionalCell.allocateInitialized, OptionalCell.allocate,
    OptionalCell.read, OptionalCell.cellType, LanguageResult.bind, LanguageResult.failure,
    LanguageResult.success, literal, Expr.weakenAt]
  rfl

example : Evaluates [] [] (compoundProgram .add false false).body
    (.inRight .word (scalar 5)) [present (scalar 888), present (scalar 5)] :=
  runStateful_evaluation_sound snapshot_completed

example : Evaluates [] [] (compoundProgram .add true false).body
    (.inLeft .word (.word invalidReason)) [present (scalar 9), present (scalar 100)] :=
  runStateful_evaluation_sound absence_completed

example : Evaluates [] [] (compoundProgram .add true true).body
    (.inLeft .word (.word rhsReason)) [present (scalar 9), present (scalar 100)] :=
  runStateful_evaluation_sound rhs_failure_completed

example (fuel : Nat) :
    ((compoundProgram .add false false).runStateful fuel).HasType (LanguageResult.resultType .word) :=
  Program.checked_runStateful_has_type snapshot_checked fuel

example (spent additional : Nat) (checkpoint : State)
    (exhausted : (compoundProgram .add false false).runStateful spent = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType (LanguageResult.resultType .word) ∧
      runStateful additional checkpoint = (compoundProgram .add false false).runStateful (spent + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound snapshot_checked).bodyHasType) exhausted additional

private def expect (program : Program) (result : Value) (store : Store) : IO Unit := do
  assertTrue program.check "assignment fixture failed Core checking"
  assertTrue (program.runStateful 250 == .done result store)
    "assignment changed snapshot order, failure priority or shared heap"
  match program.runStateful 10 with
  | .outOfFuel checkpoint =>
      assertTrue (runStateful 240 checkpoint == .done result store)
        "assignment checkpoint lost its captured snapshot or shared heap"
  | _ => throw (IO.userError "assignment fixture must suspend at fuel ten")

def run : IO Unit := do
  for operator in [LocalAssignment.Operator.add, .subtract, .multiply, .divide, .modulo,
      .bitAnd, .bitOr, .bitXor] do
    let expected : Value := .word (operator.apply (word 2) (word 3))
    expect (compoundProgram operator false false) (.inRight .word expected)
      [present (scalar 888), present expected]
    expect (compoundProgram operator true false) (.inLeft .word (.word invalidReason))
      [present (scalar 9), present (scalar 100)]
    for absent in [false, true] do
      expect (compoundProgram operator absent true) (.inLeft .word (.word rhsReason))
        [present (scalar 9), present (scalar 100)]
  expect (unaryProgram false) (.inRight .word (.word (word 2).bitNot))
    [present (scalar 888), present (.word (word 2).bitNot)]
  expect (unaryProgram true) (.inLeft .word (.word invalidReason))
    [present (scalar 9), .inLeft .word .unit]

end Tests.CoreLocalAssignment
