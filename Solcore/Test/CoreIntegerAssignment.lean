import Solcore.Core.IntegerAssignment
import Solcore.Core.FuelResumptionProperties

/-! Concrete shared-store tests distinguish the selected snapshot from a value
written by the RHS, and preserve RHS effects on both language-failure paths. -/

set_option autoImplicit false

namespace Tests.CoreIntegerAssignment

open Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Int) : Expr := .integer value
private def scalar (value : Int) : Value := .integer value
private def present (value : Value) : Value := .inRight .unit value
private def invalidReason : Word := word 63
private def rhsReason : Word := word 64

/-- Outer scope is the target reference, then the trace reference. -/
private def target : Expr :=
  .letE (.storeCell (.var 1) (.inRight .unit (literal 9))) (.var 1)

private def rhs (failure : Bool) : Expr :=
  .letE (.storeCell (.var 0) (.inRight .unit (literal 100)))
    (if failure then LanguageResult.failure .integer (.word rhsReason)
     else LanguageResult.success (literal 3))

private def next : Expr :=
  .letE (.storeCell (.var 1) (.inRight .unit (literal 888)))
    (OptionalCell.read .integer (.var 1) invalidReason)

private def withCells (absent : Bool) (body : Expr) : Program := {
  resultType := LanguageResult.resultType .integer
  body := .letE (OptionalCell.allocateInitialized .integer (literal 1))
    (.letE (if absent then OptionalCell.allocate .integer
      else OptionalCell.allocateInitialized .integer (literal 2)) body)
}

private def compoundProgram (operator : IntegerAssignment.Operator) (absent failure : Bool) : Program :=
  withCells absent (IntegerAssignment.compound .integer operator target (rhs failure) next invalidReason)

private def unaryProgram (absent : Bool) : Program :=
  withCells absent (IntegerAssignment.bitNot .integer target next invalidReason)

private def arithmeticProgram (operator : IntegerAssignment.Operator) (left right : Int) : Program := {
  resultType := LanguageResult.resultType .integer
  body := .letE (OptionalCell.allocateInitialized .integer (literal left))
    (IntegerAssignment.compound .integer operator (.var 0)
      (LanguageResult.success (literal right))
      (OptionalCell.read .integer (.var 0) invalidReason) invalidReason)
}

private theorem snapshot_checked : (compoundProgram .add false false).check = true := by
  simp [compoundProgram, withCells, target, rhs, next, IntegerAssignment.compound,
    IntegerAssignment.Operator.core, IntegerAssignment.weakenFive,
    IntegerAssignment.weakenTwo, LocalAssignment.weakenTwo, LocalAssignment.weakenThree,
    LocalAssignment.weakenFive, OptionalCell.allocateInitialized,
    OptionalCell.read, OptionalCell.cellType, LanguageResult.bind, LanguageResult.failure,
    LanguageResult.success, literal, Expr.weakenAt]
  decide

set_option maxRecDepth 4096 in
/-- `2 += RHS` uses two even though RHS writes one hundred to the same cell. -/
private theorem snapshot_completed : (compoundProgram .add false false).runStateful 250 =
    .done (.inRight .word (scalar 5)) [present (scalar 888), present (scalar 5)] := by
  simp [compoundProgram, withCells, target, rhs, next, IntegerAssignment.compound,
    IntegerAssignment.Operator.core, IntegerAssignment.weakenFive,
    IntegerAssignment.weakenTwo, LocalAssignment.weakenTwo, LocalAssignment.weakenThree,
    LocalAssignment.weakenFive, OptionalCell.allocateInitialized,
    OptionalCell.read, OptionalCell.cellType, LanguageResult.bind, LanguageResult.failure,
    LanguageResult.success, literal, Expr.weakenAt]
  rfl

set_option maxRecDepth 4096 in
/-- An absent snapshot remains invalid after a successful RHS initializes it. -/
private theorem absence_completed : (compoundProgram .add true false).runStateful 250 =
    .done (.inLeft .integer (.word invalidReason)) [present (scalar 9), present (scalar 100)] := by
  simp [compoundProgram, withCells, target, rhs, next, IntegerAssignment.compound,
    IntegerAssignment.Operator.core, IntegerAssignment.weakenFive,
    IntegerAssignment.weakenTwo, LocalAssignment.weakenTwo, LocalAssignment.weakenThree,
    LocalAssignment.weakenFive, OptionalCell.allocateInitialized, OptionalCell.allocate,
    OptionalCell.read, OptionalCell.cellType, LanguageResult.bind, LanguageResult.failure,
    LanguageResult.success, literal, Expr.weakenAt]
  rfl

set_option maxRecDepth 4096 in
/-- The RHS reason wins over the absent snapshot and retains the RHS write. -/
private theorem rhs_failure_completed : (compoundProgram .add true true).runStateful 250 =
    .done (.inLeft .integer (.word rhsReason)) [present (scalar 9), present (scalar 100)] := by
  simp [compoundProgram, withCells, target, rhs, next, IntegerAssignment.compound,
    IntegerAssignment.Operator.core, IntegerAssignment.weakenFive,
    IntegerAssignment.weakenTwo, LocalAssignment.weakenTwo, LocalAssignment.weakenThree,
    LocalAssignment.weakenFive, OptionalCell.allocateInitialized, OptionalCell.allocate,
    OptionalCell.read, OptionalCell.cellType, LanguageResult.bind, LanguageResult.failure,
    LanguageResult.success, literal, Expr.weakenAt]
  rfl

example : Evaluates [] [] (compoundProgram .add false false).body
    (.inRight .word (scalar 5)) [present (scalar 888), present (scalar 5)] :=
  runStateful_evaluation_sound snapshot_completed

example : Evaluates [] [] (compoundProgram .add true false).body
    (.inLeft .integer (.word invalidReason)) [present (scalar 9), present (scalar 100)] :=
  runStateful_evaluation_sound absence_completed

example : Evaluates [] [] (compoundProgram .add true true).body
    (.inLeft .integer (.word rhsReason)) [present (scalar 9), present (scalar 100)] :=
  runStateful_evaluation_sound rhs_failure_completed

example (fuel : Nat) :
    ((compoundProgram .add false false).runStateful fuel).HasType (LanguageResult.resultType .integer) :=
  Program.checked_runStateful_has_type snapshot_checked fuel

example (spent additional : Nat) (checkpoint : State)
    (exhausted : (compoundProgram .add false false).runStateful spent = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType (LanguageResult.resultType .integer) ∧
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
  for operator in [IntegerAssignment.Operator.add, .subtract, .multiply, .divide, .modulo,
      .bitAnd, .bitOr, .bitXor] do
    let expected : Value := .integer (operator.apply 2 3)
    expect (compoundProgram operator false false) (.inRight .word expected)
      [present (scalar 888), present expected]
    expect (compoundProgram operator true false) (.inLeft .integer (.word invalidReason))
      [present (scalar 9), present (scalar 100)]
    for absent in [false, true] do
      expect (compoundProgram operator absent true) (.inLeft .integer (.word rhsReason))
        [present (scalar 9), present (scalar 100)]
  expect (unaryProgram false) (.inRight .word (.integer (Int.not 2)))
    [present (scalar 888), present (.integer (Int.not 2))]
  expect (unaryProgram true) (.inLeft .integer (.word invalidReason))
    [present (scalar 9), .inLeft .integer .unit]
  let huge : Int := (2 : Int) ^ 1024 + 17
  for (operator, left, right, expected) in ([
      (.add, huge, huge, huge + huge),
      (.subtract, -7, 3, -10),
      (.multiply, huge, -3, -(3 * huge)),
      (.divide, -7, 3, -3),
      (.modulo, -7, 3, 2),
      (.divide, huge, 0, 0),
      (.modulo, huge, 0, 0),
      (.bitAnd, -7, 3, 1),
      (.bitOr, -7, 3, -5),
      (.bitXor, -7, 3, -6)] : List (IntegerAssignment.Operator × Int × Int × Int)) do
    expect (arithmeticProgram operator left right) (.inRight .word (.integer expected))
      [present (.integer expected)]

end Tests.CoreIntegerAssignment
