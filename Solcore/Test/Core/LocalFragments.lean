import Solcore.Core.ExactFuelProperties
import Solcore.Core.FirstOrderWeakening
import Solcore.Core.IntegerAssignment
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.LanguageResult
import Solcore.Core.BoundedSafety
import Solcore.Core.LocalAssignment
import Solcore.Core.LocalControl
import Solcore.Core.LocalFragment
import Solcore.Core.Derived
import Solcore.Resolved.LocalFragmentProperties
import Solcore.Resolved.WordLessWithIds
import Solcore.Core.Machine
import Solcore.Core.Safety
import Solcore.Core.LocalFragment.RuntimeSafety
import Solcore.Core.Correspondence
import Solcore.Core.Renaming
import Solcore.Core.LocalLoop
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.LocalSequence
import Solcore.Core.RuntimeStoreSafety

/-!
# Core local fragment tests

Local statements, loops and assignments of Core, with the fragment insertion, pair and renaming
laws, exact fuel, weakening and runtime store safety.
-/

section
-- leanmerge: from Solcore.Test.CoreExactFuelProperties
/-! Exact thresholds require a terminal path. Final-state recognition is free;
a proper nonterminal prefix does not supply a completion bound. -/

set_option autoImplicit false

namespace Tests.CoreExactFuel

open Solcore.Core

theorem already_final_needs_zero_transitions (value : Value) (store : Store) (fuel : Nat) :
    runStateful fuel (State.final value store) = .done value store ∧
    (¬ ∃ suspended, runStateful fuel (State.final value store) = .outOfFuel suspended) ∧
    ∀ steps otherValue otherStore, Steps steps (State.final value store) (State.final otherValue otherStore) →
      steps = 0 ∧ otherValue = value ∧ otherStore = store := by
  have path : Steps 0 (State.final value store) (State.final value store) := .refl
  refine ⟨path.runStateful_done_iff.mpr (Nat.zero_le _), ?_, ?_⟩
  · rw [path.runStateful_outOfFuel_iff]
    omega
  · intro steps otherValue otherStore otherPath
    exact otherPath.final_unique path

theorem a_literal_terminal_path_has_exact_one_transition_boundary
    (word : Word) (environment : Environment) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial (.word word) environment store) = .done (.word word) store ↔ 1 ≤ fuel) ∧
    ((∃ suspended, runStateful fuel (State.initial (.word word) environment store) = .outOfFuel suspended) ↔ fuel < 1) ∧
    runStateful 0 (State.initial (.word word) environment store) =
      .outOfFuel (State.initial (.word word) environment store) := by
  have path : Steps 1 (State.initial (.word word) environment store) (State.final (.word word) store) :=
    .cons .word .refl
  exact ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff, rfl⟩

theorem a_nonterminal_prefix_is_not_a_completion_bound (environment : Environment) (store : Store) :
    Steps 1 (State.initial (.unary .boolNot (.bool false)) environment store)
      ⟨.eval (.bool false) environment, [.unaryApply .boolNot], store⟩ ∧
    runStateful 1 (State.initial (.unary .boolNot (.bool false)) environment store) =
      .outOfFuel ⟨.eval (.bool false) environment, [.unaryApply .boolNot], store⟩ ∧
    Steps 3 (State.initial (.unary .boolNot (.bool false)) environment store) (State.final (.bool true) store) ∧
    runStateful 3 (State.initial (.unary .boolNot (.bool false)) environment store) = .done (.bool true) store ∧
    (1 : Nat) < 3 := by
  have path : Steps 3 (State.initial (.unary .boolNot (.bool false)) environment store) (State.final (.bool true) store) :=
    .cons .enterUnary (.cons .bool (.cons (.applyUnary rfl) .refl))
  exact ⟨.cons .enterUnary .refl, rfl, path, path.runStateful_done_iff.mpr (Nat.le_refl _), by decide⟩

theorem returning_with_a_pending_frame_is_not_final (word : Word) (store : Store) :
    Steps 0 ⟨.ret (.word word), [.unaryApply .wordNot], store⟩
      ⟨.ret (.word word), [.unaryApply .wordNot], store⟩ ∧
    runStateful 0 ⟨.ret (.word word), [.unaryApply .wordNot], store⟩ =
      .outOfFuel ⟨.ret (.word word), [.unaryApply .wordNot], store⟩ ∧
    runStateful 1 ⟨.ret (.word word), [.unaryApply .wordNot], store⟩ =
      .done (.word word.bitNot) store :=
  ⟨.refl, rfl, rfl⟩

end Tests.CoreExactFuel
end

section
-- leanmerge: from Solcore.Test.CoreFirstOrderWeakening
/-! Inserting an initializer's temporary value after a fresh lexical binder
preserves the old binder order and the exact finite first-order result. -/

set_option autoImplicit false

namespace Tests.CoreFirstOrderWeakening

open Solcore.Core

private def number : Word := Word.ofNatModulo 7
private def body : Expr := .pair (.var 0) (.var 1)
private def environment : Environment := [.word number, .bool true]
private def context : Context := [.word, .bool]
private def result : Value := .pair (.word number) (.bool true)

private theorem evaluation : Evaluates environment [] body result [] :=
  .pair (.var rfl) (.var rfl)

private theorem typed : HasType context body (.product .word .bool) :=
  .pair (.var rfl) (.var rfl)

private theorem environmentTyped : RuntimeEnvironmentHasTypes [] environment context :=
  .cons .word (.cons .bool .nil)

private theorem emptyStore : StoreHasTypes [] [] := {
  length_eq := rfl
  lookup := by intro location type found; simp at found
}

example : Evaluates [.word number, .unit, .bool true] [] (body.weakenAt 1) result [] :=
  evaluation.weakenAt_cellPayload typed (.product .word .bool)
    environmentTyped (.nil []) emptyStore 1 .unit

example : (body.weakenAt 1) = .pair (.var 0) (.var 2) := by
  simp [body, Expr.weakenAt]

example : runStateful 20
    (.initial (body.weakenAt 1) [.word number, .unit, .bool true] []) = .done result [] := by
  simp [body, Expr.weakenAt, result]
  rfl

end Tests.CoreFirstOrderWeakening
end

section
-- leanmerge: from Solcore.Test.CoreIntegerAssignment
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
end

section
-- leanmerge: from Solcore.Test.CoreLanguageResult
set_option autoImplicit false

namespace Tests.CoreLanguageResult

open Solcore.Core
open Solcore.Core.LanguageResult

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)

/-- Failure keeps the first update and bypasses the continuation's update. The
input success type is bool; the output success type is word. -/
private def failedProgram : Program := {
  resultType := resultType .word
  body :=
    .letE (.newCell .word (literal 0)) <|
    bind .word
      (.letE (.storeCell (.var 0) (literal 1)) (failure .bool (literal 41)))
      (.letE (.storeCell (.var 1) (literal 99)) (success (.loadCell (.var 2))))
}

/-- The successful continuation sees the computation's store and its payload.
The true branch changes 1 to 3; neither ignoring ordering nor ignoring the
payload can produce the expected result. -/
private def succeededProgram : Program := {
  resultType := resultType .word
  body :=
    .letE (.newCell .word (literal 0)) <|
    bind .word
      (.letE (.storeCell (.var 0) (literal 1)) (success (.bool true)))
      (.ifE (.var 0)
        (.letE
          (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (literal 2)))
          (success (.loadCell (.var 2))))
        (failure .word (literal 42)))
}

/-- Reference-valued success must preserve the referenced store location. -/
private def referenceProgram : Program := {
  resultType := resultType (.cell .word)
  body := success (.newCell .word (literal 7))
}

private theorem failedProgram_checked : failedProgram.check = true := by decide
private theorem succeededProgram_checked : succeededProgram.check = true := by decide
private theorem referenceProgram_checked : referenceProgram.check = true := by decide

private theorem failure_completed :
    failedProgram.runStateful 80 = .done (.inLeft .word (scalar 41)) [scalar 1] := by rfl

private theorem success_completed :
    succeededProgram.runStateful 80 = .done (.inRight .word (scalar 3)) [scalar 3] := by rfl

private theorem reference_completed :
    referenceProgram.runStateful 8 = .done (.inRight .word (.cellRef .word 0)) [scalar 7] := by
  rfl

example : Evaluates [] [] failedProgram.body (.inLeft .word (scalar 41)) [scalar 1] :=
  runStateful_evaluation_sound failure_completed

example : Evaluates [] [] succeededProgram.body (.inRight .word (scalar 3)) [scalar 3] :=
  runStateful_evaluation_sound success_completed

/-- The skipped continuation need not even have a finite evaluation. -/
example (body : Expr) :
    Evaluates [] [] (bind .word (failure .bool (literal 41)) body)
      (.inLeft .word (scalar 41)) [] :=
  bind_failure .word (failure_evaluates .bool .word)

/-- The result is a failure value, while all finite machine runs remain safe. -/
example (fuel : Nat) :
    (failedProgram.runStateful fuel).HasType (resultType .word) :=
  Program.checked_runStateful_has_type failedProgram_checked fuel

example :
    ∃ world outcome, RuntimeStoreHasTypes world [scalar 1] ∧
      decode? (.inLeft .word (scalar 41)) = some outcome ∧
      outcome.RuntimeHasType world .word :=
  checked_completion_decodes failedProgram_checked rfl failure_completed

example :
    ∃ world outcome, RuntimeStoreHasTypes world [scalar 3] ∧
      decode? (.inRight .word (scalar 3)) = some outcome ∧
      outcome.RuntimeHasType world .word :=
  checked_completion_decodes succeededProgram_checked rfl success_completed

example :
    ∃ world outcome, RuntimeStoreHasTypes world [scalar 7] ∧
      decode? (.inRight .word (.cellRef .word 0)) = some outcome ∧
      outcome.RuntimeHasType world (.cell .word) :=
  checked_completion_decodes referenceProgram_checked rfl reference_completed

example :
    (decode (definitions := []) (.inRight .word (.cellRef .word 0))
      (.inRight .cellRef)).RuntimeHasType
      [.word] (.cell .word) :=
  decode_runtime_hasType (.inRight (.cellRef rfl))

example : decode? (.inLeft .word .unit) = none := rfl
example : decode? (.inRight .bool (scalar 3)) = none := rfl
example : decode? (scalar 41) = none := rfl

example : LanguageResult.run failedProgram 80 = .failed (word 41) [scalar 1] := rfl
example : LanguageResult.run succeededProgram 80 = .succeeded (scalar 3) [scalar 3] := rfl
example : LanguageResult.run failedProgram 0 = .outOfFuel (.initial failedProgram.body) := rfl

example : observeResult (.done .unit []) = .invalidCarrier .unit [] := rfl
example : observeResult (.fault (.unboundVariable 0) (.initial (.var 0))) =
    .internalFault (.unboundVariable 0) (.initial (.var 0)) := rfl

example (fuel : Nat) :
    (LanguageResult.run failedProgram fuel).HasType .word :=
  checked_run_hasType failedProgram_checked rfl fuel

example (fuel : Nat) (value : Value) (store : Store) :
    LanguageResult.run failedProgram fuel ≠ .invalidCarrier value store :=
  checked_run_ne_invalidCarrier failedProgram_checked rfl

example (fuel : Nat) (error : MachineFault) (state : State) :
    LanguageResult.run failedProgram fuel ≠ .internalFault error state :=
  checked_run_ne_internalFault failedProgram_checked rfl

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def run : IO Unit := do
  assertTrue (failedProgram.check && succeededProgram.check && referenceProgram.check)
    "language result programs must pass the ordinary Core checker"
  assertTrue (failedProgram.runStateful 80 == .done (.inLeft .word (scalar 41)) [scalar 1])
    "failure must preserve earlier effects and skip continuation effects"
  assertTrue (succeededProgram.runStateful 80 == .done (.inRight .word (scalar 3)) [scalar 3])
    "success must pass the payload and updated store to the continuation"
  assertTrue (referenceProgram.runStateful 8 ==
      .done (.inRight .word (.cellRef .word 0)) [scalar 7])
    "success must retain cell identity in its payload"
  assertTrue (decode? (.inLeft .word (scalar 41)) == some (.failed (word 41)))
    "completed failure must decode as a language failure reason"
  assertTrue (decode? (.inRight .word (scalar 3)) == some (.succeeded (scalar 3)))
    "completed success must decode its original payload"
  assertTrue ((decode? (.inLeft .word .unit)).isNone &&
      (decode? (.inRight .bool (scalar 3))).isNone && (decode? (scalar 41)).isNone)
    "malformed carriers must not decode as success or language failure"
  assertTrue (LanguageResult.run failedProgram 80 == .failed (word 41) [scalar 1])
    "the observation facade must preserve language failure and its final store"
  assertTrue (LanguageResult.run succeededProgram 80 == .succeeded (scalar 3) [scalar 3])
    "the observation facade must preserve successful payloads and their final store"
  assertTrue (LanguageResult.run failedProgram 0 == .outOfFuel (.initial failedProgram.body))
    "the observation facade must retain the exact exhaustion checkpoint"
  assertTrue (observeResult (.done .unit []) == .invalidCarrier .unit [])
    "a malformed completion must remain distinct from language failure"
  assertTrue (observeResult (.fault (.unboundVariable 0) (.initial (.var 0))) ==
      .internalFault (.unboundVariable 0) (.initial (.var 0)))
    "the observation facade must retain the internal fault and its state"

end Tests.CoreLanguageResult
end

section
-- leanmerge: from Solcore.Test.CoreLocalAssignment
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
end

section
-- leanmerge: from Solcore.Test.CoreLocalControl
/-! Control sums retain condition effects, early returns, failures and the
heap shared with scoped blocks. Every completion here has an actual finite run. -/

set_option autoImplicit false

namespace Tests.CoreLocalControl

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def reason : Word := word 31

example {environment : Environment} {store : Store} (next : Expr) :
    Evaluates environment store
      (LocalControl.sequence .word (LocalControl.returned (literal 7)) next)
      (.inRight .word (.inRight .unit (scalar 7))) store :=
  LocalControl.sequence_returned .word (LocalControl.returned_evaluates .word)

private def conditionalProgram (select : Bool) : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (LocalControl.finish .word
      (LocalControl.conditional .word
        (LanguageResult.success (.letE (.storeCell (.var 0) (literal 11)) (.bool select)))
        (LocalControl.returned (.loadCell (.var 0)))
        (LocalControl.returned
          (.letE (.storeCell (.var 0) (literal 17)) (.loadCell (.var 1)))))
      (LanguageResult.failure .word (.word reason)))
}

example (select : Bool) : (conditionalProgram select).check = true := by
  cases select <;> simp [conditionalProgram, LocalControl.finish, LocalControl.conditional, LocalControl.returned,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  all_goals decide

example : (conditionalProgram true).runStateful 100 =
    .done (.inRight .word (scalar 11)) [scalar 11] := by
  simp [conditionalProgram, LocalControl.finish, LocalControl.conditional, LocalControl.returned,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

example : (conditionalProgram false).runStateful 100 =
    .done (.inRight .word (scalar 17)) [scalar 17] := by
  simp [conditionalProgram, LocalControl.finish, LocalControl.conditional, LocalControl.returned,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

private def conditionFailureProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (LocalControl.finish .word
      (LocalControl.sequence .word
        (LocalControl.conditional .word
          (LanguageResult.failure .bool
            (.letE (.storeCell (.var 0) (literal 11)) (.word reason)))
          (LocalControl.returned (.letE (.storeCell (.var 0) (literal 99)) (literal 7)))
          (LocalControl.returned (.letE (.storeCell (.var 0) (literal 98)) (literal 8))))
        (LocalControl.returned (.letE (.storeCell (.var 0) (literal 97)) (literal 9))))
      (LanguageResult.failure .word (.word reason)))
}

example : conditionFailureProgram.check = true := by
  simp [conditionFailureProgram, LocalControl.finish, LocalControl.sequence, LocalControl.conditional,
    LocalControl.returned, LanguageResult.bind, LanguageResult.failure, LanguageResult.success,
    Expr.weakenAt, literal]
  decide

/-- Condition failure keeps its write and skips both branches and the tail. -/
example : conditionFailureProgram.runStateful 100 =
    .done (.inLeft .word (.word reason)) [scalar 11] := by
  simp [conditionFailureProgram, LocalControl.finish, LocalControl.sequence, LocalControl.conditional,
    LocalControl.returned, LanguageResult.bind, LanguageResult.failure, LanguageResult.success,
    Expr.weakenAt, literal]
  rfl

private def scopedFallthroughProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (LocalControl.finish .word
      (LocalControl.sequence .word
        (LocalSequence.letInitialized (LocalControl.controlType .word) .word
          (LanguageResult.success (literal 7))
          (LocalSequence.discard (LocalControl.controlType .word)
            (OptionalCell.write (.var 0) (literal 9))
            (.letE (.storeCell (.var 1) (literal 11)) (LocalControl.fallthrough .word))))
        (LocalControl.returned (.loadCell (.var 0))))
      (LanguageResult.failure .word (.word reason)))
}

example : scopedFallthroughProgram.check = true := by
  simp [scopedFallthroughProgram, LocalControl.finish, LocalControl.sequence, LocalControl.returned,
    LocalControl.fallthrough, LocalSequence.letInitialized, LocalSequence.discard,
    OptionalCell.allocateInitialized, OptionalCell.write, LanguageResult.bind,
    LanguageResult.failure, LanguageResult.success, Expr.weakenAt, literal]
  decide

/-- The block's local reference stays out of the outer lexical environment;
its allocation and writes remain in the shared heap. The tail reads the outer
counter, rather than the block's optional cell. -/
example : scopedFallthroughProgram.runStateful 150 =
    .done (.inRight .word (scalar 11)) [scalar 11, .inRight .unit (scalar 9)] := by
  simp [scopedFallthroughProgram, LocalControl.finish, LocalControl.sequence, LocalControl.returned,
    LocalControl.fallthrough, LocalSequence.letInitialized, LocalSequence.discard,
    OptionalCell.allocateInitialized, OptionalCell.write, LanguageResult.bind,
    LanguageResult.failure, LanguageResult.success, Expr.weakenAt, literal]
  rfl

private def earlyReturnProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (LocalControl.finish .word
      (LocalControl.sequence .word
        (LocalSequence.letInitialized (LocalControl.controlType .word) .word
          (LanguageResult.success (literal 7))
          (LocalControl.conditional .word (LanguageResult.success (.bool true))
            (LocalControl.returnValue .word (OptionalCell.read .word (.var 0) reason))
            (LocalControl.fallthrough .word)))
        (LocalControl.returned (.letE (.storeCell (.var 0) (literal 99)) (.loadCell (.var 1)))))
      (LanguageResult.failure .word (.word reason)))
}

private theorem earlyReturn_checked : earlyReturnProgram.check = true := by
  simp [earlyReturnProgram, LocalControl.finish, LocalControl.sequence, LocalControl.conditional,
    LocalControl.returnValue, LocalControl.returned, LocalControl.fallthrough,
    LocalSequence.letInitialized, OptionalCell.allocateInitialized, OptionalCell.read,
    LanguageResult.bind, LanguageResult.failure, LanguageResult.success, Expr.weakenAt, literal]
  decide

private theorem earlyReturn_completed : earlyReturnProgram.runStateful 150 =
    .done (.inRight .word (scalar 7)) [scalar 3, .inRight .unit (scalar 7)] := by
  simp [earlyReturnProgram, LocalControl.finish, LocalControl.sequence, LocalControl.conditional,
    LocalControl.returnValue, LocalControl.returned, LocalControl.fallthrough,
    LocalSequence.letInitialized, OptionalCell.allocateInitialized, OptionalCell.read,
    LanguageResult.bind, LanguageResult.failure, LanguageResult.success, Expr.weakenAt, literal]
  rfl

/-- A successful Unit fallthrough is chosen explicitly at the function boundary. -/
example : Evaluates [] []
    (LocalControl.finish .unit (LocalControl.fallthrough .unit) (LanguageResult.success .unit))
    (.inRight .word .unit) [] := by
  apply LocalControl.finish_fallthrough .unit (LocalControl.fallthrough_evaluates _ _ _)
  simp [LanguageResult.success, Expr.weakenAt]
  exact .inRight .unit

/-- A missing-return fallback is a normal language failure, rather than an
internal machine fault, and it executes after the block's preceding effects. -/
example : Evaluates [.cellRef .word 0] [scalar 3]
    (LocalControl.finish .word
      (.letE (.storeCell (.var 0) (literal 11)) (LocalControl.fallthrough .word))
      (LanguageResult.failure .word
        (.letE (.storeCell (.var 0) (literal 17)) (.word reason))))
    (.inLeft .word (.word reason)) [scalar 17] := by
  apply LocalControl.finish_fallthrough .word
  · exact .letE (.storeCell (.var rfl) rfl .word rfl)
      (LocalControl.fallthrough_evaluates _ _ _)
  · simp [LanguageResult.failure, Expr.weakenAt, literal]
    exact .inLeft (.letE (.storeCell (.var rfl) rfl .word rfl) .word)

example (fuel : Nat) : (earlyReturnProgram.runStateful fuel).HasType earlyReturnProgram.resultType :=
  Program.checked_runStateful_has_type earlyReturn_checked fuel

example (fuel additional : Nat) (checkpoint : State)
    (exhausted : earlyReturnProgram.runStateful fuel = .outOfFuel checkpoint) :
    runStateful additional checkpoint = earlyReturnProgram.runStateful (fuel + additional) :=
  runStateful_resume exhausted additional

example : ∃ required, ∀ fuel, required ≤ fuel → earlyReturnProgram.runStateful fuel =
    .done (.inRight .word (scalar 7)) [scalar 3, .inRight .unit (scalar 7)] :=
  evaluation_runStateful_complete_with_sufficient_fuel
    (runStateful_evaluation_sound earlyReturn_completed)

end Tests.CoreLocalControl
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentExactInsertionBoundary
/-! Exact final costs survive insertion; genuine let checkpoints do not become
equal. Every transported outer continuation remains pending and unchanged. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentExactInsertionBoundary

open Solcore.Core

private def less : Expr := .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
private def environment (left right : Word) (tail : Environment) : Environment := .word right :: .word left :: tail
private def result (left right : Word) : Value := .bool (decide (left < right))
private theorem lessFragment : less.LocalFragment := .letE .var (.letE .var (.binary .var .var))
private theorem shiftedLess : less.weakenAt 0 =
    .letE (.var 2) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1))) := by
  simp [less, Expr.weakenAt]
private def originalCheckpoint (left right : Word) (tail : Environment) (store : Store) : State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
    (environment left right tail)], store⟩
private def shiftedCheckpoint (left right : Word) (tail : Environment) (inserted : Value) (store : Store) : State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
    (inserted :: environment left right tail)], store⟩
private theorem originalPath (left right : Word) (tail : Environment) (store : Store) :
    Steps 11 (State.initial less (environment left right tail) store) (State.final (result left right) store) :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet
    (.cons .enterLet (.cons (.var rfl) (.cons .bindLet
      (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight
        (.cons (.var rfl) (.cons (.applyBinary rfl) .refl))))))))))

theorem ordered_word_less_expansion_retains_eleven_steps_and_exact_closed_path_equivalence
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) (cost : Nat) :
    less = (Expr.var 1).wordLt (.var 0) ∧ less.LocalFragment ∧
    Steps 11 (State.initial less (environment left right tail) store) (State.final (result left right) store) ∧
    Steps 11 (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store)
      (State.final (result left right) store) ∧
    (Steps cost (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store)
        (State.final (result left right) store) ↔
      Steps cost (State.initial less (environment left right tail) store) (State.final (result left right) store)) := by
  refine ⟨?_, lessFragment, originalPath left right tail store,
    (originalPath left right tail store).weakenAt_zero_localFragment lessFragment inserted [],
    lessFragment.steps_insert_iff [] (environment left right tail) inserted⟩
  simp [less, Expr.wordLt_expansion, Expr.weakenAt]

theorem completion_and_exhaustion_thresholds_match_without_equating_full_results
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial less (environment left right tail) store) =
      .done (result left right) store ↔ 11 ≤ fuel) ∧
    (runStateful fuel (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) =
      .done (result left right) store ↔ 11 ≤ fuel) ∧
    ((∃ state, runStateful fuel (State.initial less (environment left right tail) store) = .outOfFuel state) ↔
      fuel < 11) ∧
    ((∃ state, runStateful fuel (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) =
      .outOfFuel state) ↔ fuel < 11) := by
  have original := originalPath left right tail store
  have shifted := original.weakenAt_zero_localFragment lessFragment inserted []
  exact ⟨original.runStateful_done_iff, shifted.runStateful_done_iff,
    original.runStateful_outOfFuel_iff, shifted.runStateful_outOfFuel_iff⟩

theorem distinct_genuine_let_checkpoints_resume_independently_with_nine_remaining_steps
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) (additional : Nat) :
    runStateful 2 (State.initial less (environment left right tail) store) =
      .outOfFuel (originalCheckpoint left right tail store) ∧
    runStateful 2 (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) =
      .outOfFuel (shiftedCheckpoint left right tail inserted store) ∧
    originalCheckpoint left right tail store ≠ shiftedCheckpoint left right tail inserted store ∧
    Steps 9 (originalCheckpoint left right tail store) (State.final (result left right) store) ∧
    Steps 9 (shiftedCheckpoint left right tail inserted store) (State.final (result left right) store) ∧
    runStateful additional (originalCheckpoint left right tail store) =
      runStateful (2 + additional) (State.initial less (environment left right tail) store) ∧
    runStateful additional (shiftedCheckpoint left right tail inserted store) =
      runStateful (2 + additional) (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) ∧
    (runStateful additional (shiftedCheckpoint left right tail inserted store) =
      .done (result left right) store ↔ 9 ≤ additional) := by
  have original := originalPath left right tail store
  have shifted := original.weakenAt_zero_localFragment lessFragment inserted []
  have first : runStateful 2 (State.initial less (environment left right tail) store) =
      .outOfFuel (originalCheckpoint left right tail store) := rfl
  have second : runStateful 2 (State.initial (less.weakenAt 0) (inserted :: environment left right tail) store) =
      .outOfFuel (shiftedCheckpoint left right tail inserted store) := by rw [shiftedLess]; rfl
  refine ⟨first, second, ?_, (original.residual_of_outOfFuel first).2, (shifted.residual_of_outOfFuel second).2,
    runStateful_resume first additional, runStateful_resume second additional, shifted.resumed_done_iff second⟩
  intro same
  cases same

theorem arbitrary_nonempty_continuations_are_retained_not_rewritten_or_executed
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) (outer : List Frame) :
    Steps 11 ⟨.eval less (environment left right tail), .unaryApply .boolNot :: outer, store⟩
      ⟨.ret (result left right), .unaryApply .boolNot :: outer, store⟩ ∧
    Steps 11 ⟨.eval (less.weakenAt 0) (inserted :: environment left right tail), .unaryApply .boolNot :: outer, store⟩
      ⟨.ret (result left right), .unaryApply .boolNot :: outer, store⟩ ∧
    Steps 12 ⟨.eval (less.weakenAt 0) (inserted :: environment left right tail), .unaryApply .boolNot :: outer, store⟩
      ⟨.ret (.bool (!(decide (left < right)))), outer, store⟩ := by
  have shiftedClosed := (originalPath left right tail store).weakenAt_zero_localFragment lessFragment inserted []
  have original := shiftedClosed.reflect_weakenAt_zero_localFragment lessFragment (.unaryApply .boolNot :: outer)
  have shifted := lessFragment.steps_insert [] (environment left right tail) inserted
    (originalPath left right tail store) (.unaryApply .boolNot :: outer)
  exact ⟨original, shifted, shifted.trans (.cons (.applyUnary rfl) .refl)⟩

theorem eleven_fuel_still_exhausts_when_the_retained_outer_negation_has_not_run
    (left right : Word) (tail : Environment) (inserted : Value) (store : Store) :
    runStateful 11 ⟨.eval (less.weakenAt 0) (inserted :: environment left right tail), [.unaryApply .boolNot], store⟩ =
      .outOfFuel ⟨.ret (result left right), [.unaryApply .boolNot], store⟩ ∧
    runStateful 12 ⟨.eval (less.weakenAt 0) (inserted :: environment left right tail), [.unaryApply .boolNot], store⟩ =
      .done (.bool (!(decide (left < right)))) store := by
  have paths := arbitrary_nonempty_continuations_are_retained_not_rewritten_or_executed left right tail inserted store []
  exact ⟨runStateful_outOfFuel_complete paths.2.1 rfl, paths.2.2.runStateful_done_iff.mpr (by decide)⟩

private def badBranch : Expr := .unary .wordNot (.bool false)
private def skipped : Expr := .ifE (.bool true) .unit badBranch
private theorem skippedFragment : skipped.LocalFragment := .ifE .bool .unit (.unary .bool)
private theorem skippedPath (environment : Environment) (store : Store) :
    Steps 4 (State.initial skipped environment store) (State.final .unit store) :=
  .cons .enterIf (.cons .bool (.cons .chooseTrue (.cons .unit .refl)))

theorem unselected_structural_but_ill_typed_children_do_not_contribute_path_cost
    (environment : Environment) (inserted : Value) (store : Store) (context : Context) (definitions : DataEnvironment) :
    skipped.LocalFragment ∧ (∀ type, ¬HasType context skipped type definitions) ∧
    Evaluates environment store skipped .unit store ∧
    (∀ continuation,
      Steps 4 ⟨.eval skipped environment, continuation, store⟩ ⟨.ret .unit, continuation, store⟩ ∧
      Steps 4 ⟨.eval (skipped.weakenAt 0) (inserted :: environment), continuation, store⟩
        ⟨.ret .unit, continuation, store⟩) := by
  have evaluation : Evaluates environment store skipped .unit store := .ifTrue .bool .unit
  obtain ⟨cost, paired⟩ := skippedFragment.insertion_paths [] environment inserted evaluation
  have sameCost := ((skippedPath environment store).final_unique (paired []).1).1
  refine ⟨skippedFragment, ?_, evaluation, ?_⟩
  · intro type typing
    cases typing with
    | ifE _ _ rejected =>
        cases rejected with
        | unary child => cases child
  · exact sameCost ▸ paired

end Tests.CoreLocalFragmentExactInsertionBoundary
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentExactInsertionProperties
/-! Independent transition chains fix numeric costs before insertion. The same
outer continuation is retained without executing its frames, and runtime values
and stores need no typing, freshness, or allocation premises. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentExactInsertion

open Solcore Solcore.Core

private def arithmetic (cutoff : Nat) : Expr :=
  .unary .wordNot (.binary .wordSub (.var cutoff) (.var (cutoff + 1)))
private theorem arithmeticLocal (cutoff : Nat) : (arithmetic cutoff).LocalFragment := .unary (.binary .var .var)
private theorem arithmeticEvaluates (leading suffix : Environment) (left right : Word) (store : Store) :
    Evaluates (leading ++ .word left :: .word right :: suffix) store (arithmetic leading.length)
      (.word (left.sub right).bitNot) store := by
  have first : (leading ++ .word left :: .word right :: suffix)[leading.length]? = some (.word left) := by simp
  have second : (leading ++ .word left :: .word right :: suffix)[leading.length + 1]? = some (.word right) := by simp
  exact .unary (.binary (.var first) (.var second) rfl) rfl
private theorem arithmeticPath (leading suffix : Environment) (left right : Word) (store : Store) :
    Steps 7 (State.initial (arithmetic leading.length) (leading ++ .word left :: .word right :: suffix) store)
      (State.final (.word (left.sub right).bitNot) store) := by
  have first : (leading ++ .word left :: .word right :: suffix)[leading.length]? = some (.word left) := by simp
  have second : (leading ++ .word left :: .word right :: suffix)[leading.length + 1]? = some (.word right) := by simp
  exact .cons .enterUnary (.cons .enterBinary (.cons (.var first) (.cons .enterBinaryRight
    (.cons (.var second) (.cons (.applyBinary (result := .word (left.sub right)) rfl) (.cons (.applyUnary rfl) .refl))))))

private def nested : Expr := .letE (.var 1) (.letE (.var 0) (.var 2))
private theorem nestedLocal : nested.LocalFragment := .letE .var (.letE .var .var)
private theorem nestedPath (retained bound : Value) (suffix : Environment) (store : Store) :
    Steps 7 (State.initial nested (retained :: bound :: suffix) store) (State.final retained store) :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet
    (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))

private def conditional (choice : Bool) (left right : Word) : Expr :=
  .ifE (.bool choice) (.binary .wordMul (.word left) (.word right)) (.var 0)
private theorem conditionalLocal (choice : Bool) (left right : Word) : (conditional choice left right).LocalFragment :=
  .ifE .bool (.binary .word .word) .var
private theorem conditionalPath (choice : Bool) (left right : Word) (value : Value) (suffix : Environment) (store : Store) :
    Steps (if choice then 8 else 4) (State.initial (conditional choice left right) (value :: suffix) store)
      (State.final (if choice then .word (left.mul right) else value) store) := by
  cases choice
  · exact .cons .enterIf (.cons .bool (.cons .chooseFalse (.cons (.var rfl) .refl)))
  · exact .cons .enterIf (.cons .bool (.cons .chooseTrue (.cons .enterBinary
      (.cons .word (.cons .enterBinaryRight (.cons .word (.cons (.applyBinary rfl) .refl)))))))

private def skipped : Expr := .ifE (.bool true) (.var 0) (.binary .wordSub (.bool true) .unit)
private theorem skippedLocal : skipped.LocalFragment := .ifE .bool .var (.binary .bool .unit)
private theorem skippedPath (value : Value) (suffix : Environment) (store : Store) :
    Steps 4 (State.initial skipped (value :: suffix) store) (State.final value store) :=
  .cons .enterIf (.cons .bool (.cons .chooseTrue (.cons (.var rfl) .refl)))

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ExactInsertion", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def named : Resolved.Expr := .wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) (.var (ident 1))
private def ordered : Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem orderedLowered : Resolved.Lowers [ident 0, ident 1] named ordered := by
  have left : Resolved.Lowers [ident 0, ident 1] (.var (ident 0)) (.var 0) := .var .head
  have right : Resolved.Lowers [ident 0, ident 1] (.var (ident 1)) (.var 1) := .var (.tail (by decide) .head)
  simpa [named, ordered, Expr.wordLt_expansion, Expr.weakenAt] using
    left.wordLtWithIds (leftId := ident 2) (rightId := ident 0) right (by decide) (by decide)
private theorem orderedPath (left right : Word) (store : Store) :
    Steps 11 (State.initial ordered [.word left, .word right] store)
      (State.final (.bool (decide (left < right))) store) :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
    (.cons .bindLet (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight
      (.cons (.var rfl) (.cons (.applyBinary rfl) .refl))))))))))

theorem unit_bool_and_word_constants_cost_one_under_any_retained_prefix
    (leading suffix : Environment) (inserted : Value) (choice : Bool) (word : Word)
    (store : Store) (continuation : List Frame) :
    Steps 1 ⟨.eval .unit (leading ++ inserted :: suffix), continuation, store⟩ ⟨.ret .unit, continuation, store⟩ ∧
    Steps 1 ⟨.eval (.bool choice) (leading ++ inserted :: suffix), continuation, store⟩
      ⟨.ret (.bool choice), continuation, store⟩ ∧
    Steps 1 ⟨.eval (.word word) (leading ++ inserted :: suffix), continuation, store⟩
      ⟨.ret (.word word), continuation, store⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Expr.weakenAt] using Expr.LocalFragment.unit.steps_insert leading suffix inserted
      (show Steps 1 (State.initial .unit (leading ++ suffix) store) (State.final .unit store) from .cons .unit .refl) continuation
  · simpa only [Expr.weakenAt] using Expr.LocalFragment.bool.steps_insert leading suffix inserted
      (show Steps 1 (State.initial (.bool choice) (leading ++ suffix) store) (State.final (.bool choice) store)
        from .cons .bool .refl) continuation
  · simpa only [Expr.weakenAt] using Expr.LocalFragment.word.steps_insert leading suffix inserted
      (show Steps 1 (State.initial (.word word) (leading ++ suffix) store) (State.final (.word word) store)
        from .cons .word .refl) continuation

theorem arbitrary_return_values_keep_one_step_and_exact_closed_path_reflection
    (leading suffix : Environment) (value inserted : Value) (store : Store) (continuation : List Frame) :
    Steps 1 ⟨.eval ((Expr.var leading.length).weakenAt leading.length) (leading ++ inserted :: value :: suffix),
      continuation, store⟩ ⟨.ret value, continuation, store⟩ ∧
    Steps 1 ⟨.eval (.var leading.length) (leading ++ value :: suffix), continuation, store⟩
      ⟨.ret value, continuation, store⟩ ∧
    (Steps 1 (State.initial ((Expr.var leading.length).weakenAt leading.length) (leading ++ inserted :: value :: suffix) store)
      (State.final value store) ↔
      Steps 1 (State.initial (.var leading.length) (leading ++ value :: suffix) store) (State.final value store)) := by
  have fragment : (Expr.var leading.length).LocalFragment := .var
  have original : Steps 1 (State.initial (.var leading.length) (leading ++ value :: suffix) store) (State.final value store) :=
    .cons (.var (by simp)) .refl
  have shifted := fragment.steps_insert leading (value :: suffix) inserted original []
  exact ⟨fragment.steps_insert leading (value :: suffix) inserted original continuation,
    fragment.steps_reflect_insert leading (value :: suffix) inserted shifted continuation,
    fragment.steps_insert_iff leading (value :: suffix) inserted⟩

theorem paired_unary_binary_paths_choose_seven_before_the_arbitrary_continuation
    (leading suffix : Environment) (left right : Word) (inserted : Value) (store : Store) :
    ∃ cost, cost = 7 ∧ ∀ continuation,
      Steps cost ⟨.eval (arithmetic leading.length) (leading ++ .word left :: .word right :: suffix), continuation, store⟩
        ⟨.ret (.word (left.sub right).bitNot), continuation, store⟩ ∧
      Steps cost ⟨.eval ((arithmetic leading.length).weakenAt leading.length)
          (leading ++ inserted :: .word left :: .word right :: suffix), continuation, store⟩
        ⟨.ret (.word (left.sub right).bitNot), continuation, store⟩ := by
  obtain ⟨cost, paths⟩ := (arithmeticLocal leading.length).insertion_paths leading
    (.word left :: .word right :: suffix) inserted (arithmeticEvaluates leading suffix left right store)
  have exactCost := ((arithmeticPath leading suffix left right store).final_unique (paths []).1).1
  exact ⟨cost, exactCost.symm, paths⟩

theorem nested_lets_keep_seven_steps_at_nonzero_insertion_depth
    (retained bound inserted : Value) (suffix : Environment) (store : Store) (continuation : List Frame) :
    Steps 7 ⟨.eval (nested.weakenAt 1) (retained :: inserted :: bound :: suffix), continuation, store⟩
      ⟨.ret retained, continuation, store⟩ ∧
    Steps 7 ⟨.eval nested (retained :: bound :: suffix), continuation, store⟩ ⟨.ret retained, continuation, store⟩ := by
  have shifted := nestedLocal.steps_insert [retained] (bound :: suffix) inserted (nestedPath retained bound suffix store) []
  exact ⟨nestedLocal.steps_insert [retained] (bound :: suffix) inserted (nestedPath retained bound suffix store) continuation,
    nestedLocal.steps_reflect_insert [retained] (bound :: suffix) inserted shifted continuation⟩

theorem both_conditional_paths_preserve_their_distinct_exact_costs
    (choice : Bool) (left right : Word) (value inserted : Value) (suffix : Environment)
    (store : Store) (continuation : List Frame) :
    Steps (if choice then 8 else 4)
      ⟨.eval ((conditional choice left right).weakenAt 0) (inserted :: value :: suffix), continuation, store⟩
      ⟨.ret (if choice then .word (left.mul right) else value), continuation, store⟩ ∧
    Steps (if choice then 8 else 4)
      ⟨.eval (conditional choice left right) (value :: suffix), continuation, store⟩
      ⟨.ret (if choice then .word (left.mul right) else value), continuation, store⟩ := by
  have original := conditionalPath choice left right value suffix store
  have shifted := original.weakenAt_zero_localFragment (conditionalLocal choice left right) inserted []
  exact ⟨original.weakenAt_zero_localFragment (conditionalLocal choice left right) inserted continuation,
    shifted.reflect_weakenAt_zero_localFragment (conditionalLocal choice left right) continuation⟩

theorem shifted_and_original_closed_runs_have_identical_exact_fuel_thresholds
    (choice : Bool) (left right : Word) (value inserted : Value) (suffix : Environment) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial ((conditional choice left right).weakenAt 0) (inserted :: value :: suffix) store) =
      .done (if choice then .word (left.mul right) else value) store ↔ (if choice then 8 else 4) ≤ fuel) ∧
    ((∃ checkpoint, runStateful fuel
      (State.initial ((conditional choice left right).weakenAt 0) (inserted :: value :: suffix) store) = .outOfFuel checkpoint) ↔
      fuel < (if choice then 8 else 4)) ∧
    (runStateful fuel (State.initial (conditional choice left right) (value :: suffix) store) =
      .done (if choice then .word (left.mul right) else value) store ↔ (if choice then 8 else 4) ≤ fuel) := by
  have paths := both_conditional_paths_preserve_their_distinct_exact_costs choice left right value inserted suffix store []
  exact ⟨paths.1.runStateful_done_iff, paths.1.runStateful_outOfFuel_iff, paths.2.runStateful_done_iff⟩

theorem skipped_local_bad_type_adds_no_cost_and_outer_frames_remain_unexecuted
    (value inserted : Value) (suffix : Environment) (store : Store) :
    skipped.LocalFragment ∧ Steps 4
      ⟨.eval (skipped.weakenAt 0) (inserted :: value :: suffix), [.unaryApply .wordNot], store⟩
      ⟨.ret value, [.unaryApply .wordNot], store⟩ :=
  ⟨skippedLocal, (skippedPath value suffix store).weakenAt_zero_localFragment skippedLocal inserted [.unaryApply .wordNot]⟩

theorem lowered_ordered_comparison_preserves_eleven_steps_on_nonempty_stores
    (left right : Word) (inserted : Value) (store : Store) (continuation : List Frame) :
    Resolved.Lowers [ident 0, ident 1] named ordered ∧ ordered.LocalFragment ∧
    Steps 11 (State.initial ordered [.word left, .word right] (.unit :: store))
      (State.final (.bool (decide (left < right))) (.unit :: store)) ∧
    Steps 11 ⟨.eval (ordered.weakenAt 0) [inserted, .word left, .word right], continuation, .unit :: store⟩
      ⟨.ret (.bool (decide (left < right))), continuation, .unit :: store⟩ :=
  ⟨orderedLowered, orderedLowered.localFragment, orderedPath left right (.unit :: store),
    (orderedPath left right (.unit :: store)).weakenAt_zero_localFragment orderedLowered.localFragment inserted continuation⟩

end Tests.CoreLocalFragmentExactInsertion
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentInsertionBoundary
/-! Insertion equivalence has a syntactic boundary: creation captures the
environment, every written branch matters, and suspended states remain distinct. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentInsertionBoundary

open Solcore.Core

private def identity : Expr := .lambda .unit .unit (.var 0)
private def skip (unselected : Expr) : Expr := .ifE (.bool true) .unit unselected
private theorem weakenedVar : (Expr.var 0).weakenAt 0 = .var 1 := by simp [Expr.weakenAt]
private theorem weakenedIdentity : identity.weakenAt 0 = identity := by simp [identity, Expr.weakenAt]

theorem unshifted_reference_reads_the_inserted_value_instead_of_the_old_one
    (old inserted : Value) (different : inserted ≠ old) (tail : Environment) (store : Store) :
    Expr.LocalFragment (.var 0) ∧
    Evaluates (old :: tail) store (.var 0) old store ∧
    Evaluates (inserted :: old :: tail) store (.var 0) inserted store ∧
    Evaluates (inserted :: old :: tail) store ((Expr.var 0).weakenAt 0) old store ∧
    runStateful 1 (State.initial (.var 0) (old :: tail) store) ≠
      runStateful 1 (State.initial (.var 0) (inserted :: old :: tail) store) := by
  have original : Evaluates (old :: tail) store (.var 0) old store := .var rfl
  refine ⟨.var, original, .var rfl, original.weakenAt_zero_localFragment .var inserted, ?_⟩
  intro same
  exact different (StatefulRunResult.done.inj same).1.symm

theorem syntactic_membership_does_not_supply_a_missing_variable
    (inserted : Value) (store finalStore : Store) (result : Value) :
    Expr.LocalFragment (.var 0) ∧ Expr.LocalFragment ((Expr.var 0).weakenAt 0) ∧
    ¬Evaluates [] store (.var 0) result finalStore ∧
    ¬Evaluates [inserted] store ((Expr.var 0).weakenAt 0) result finalStore := by
  have absent : ¬Evaluates [] store (.var 0) result finalStore := by
    intro evaluation
    cases evaluation with
    | var lookup => cases lookup
  refine ⟨.var, Expr.LocalFragment.weakenAt .var 0, absent, ?_⟩
  intro evaluation
  exact absent ((Expr.LocalFragment.var.evaluates_weaken_zero_iff [] inserted).mp evaluation)

theorem cell_free_lambda_creation_changes_captures_without_changing_the_store
    (inserted : Value) (environment : Environment) (store : Store) :
    Expr.CellFree identity ∧ ¬Expr.LocalFragment identity ∧
    identity.weakenAt 0 = identity ∧
    Evaluates environment store identity (.closure .unit .unit (.var 0) environment) store ∧
    Evaluates (inserted :: environment) store (identity.weakenAt 0)
      (.closure .unit .unit (.var 0) (inserted :: environment)) store ∧
    ¬Evaluates (inserted :: environment) store (identity.weakenAt 0)
      (.closure .unit .unit (.var 0) environment) store ∧
    runStateful 1 (State.initial identity environment store) ≠
      runStateful 1 (State.initial (identity.weakenAt 0) (inserted :: environment) store) := by
  have different : environment ≠ inserted :: environment := by
    intro same
    have lengths := congrArg List.length same
    simp at lengths
  have captures : (Value.closure .unit .unit (.var 0) environment) ≠
      .closure .unit .unit (.var 0) (inserted :: environment) := by
    intro same
    exact different (Value.closure.inj same).2.2.2
  have actual : Evaluates (inserted :: environment) store (identity.weakenAt 0)
      (.closure .unit .unit (.var 0) (inserted :: environment)) store := by
    rw [weakenedIdentity]
    exact .lambda
  refine ⟨.lambda .var, ?_, weakenedIdentity, .lambda, actual, ?_, ?_⟩
  · intro fragment
    cases fragment
  · intro evaluation
    exact captures (evaluation_deterministic evaluation actual).1
  · rw [weakenedIdentity]
    intro same
    exact captures (StatefulRunResult.done.inj same).1

private theorem skipped_not_local {unselected : Expr} (outside : ¬Expr.LocalFragment unselected) :
    ¬Expr.LocalFragment (skip unselected) := by
  intro fragment
  cases fragment with
  | ifE _ _ branch => exact outside branch

theorem every_written_branch_is_required_even_when_raw_execution_skips_it
    (unselected : Expr) (outside : ¬Expr.LocalFragment unselected) (environment : Environment) (store : Store) :
    ¬Expr.LocalFragment (skip unselected) ∧
    Evaluates environment store (skip unselected) .unit store ∧
    runStateful 4 (State.initial (skip unselected) environment store) = .done .unit store :=
  ⟨skipped_not_local outside, .ifTrue .bool .unit, rfl⟩

theorem skipped_lambda_application_and_cell_access_all_remain_outside_the_fragment
    (environment : Environment) (store : Store) :
    Expr.CellFree (.apply identity .unit) ∧
    ¬Expr.LocalFragment (skip identity) ∧
    ¬Expr.LocalFragment (skip (.apply identity .unit)) ∧
    ¬Expr.LocalFragment (skip (.loadCell (.var 0))) ∧
    runStateful 4 (State.initial (skip identity) environment store) = .done .unit store ∧
    runStateful 4 (State.initial (skip (.apply identity .unit)) environment store) = .done .unit store ∧
    runStateful 4 (State.initial (skip (.loadCell (.var 0))) environment store) = .done .unit store := by
  have lambdaOutside : ¬Expr.LocalFragment identity := by intro fragment; cases fragment
  have callOutside : ¬Expr.LocalFragment (.apply identity .unit) := by intro fragment; cases fragment
  have cellOutside : ¬Expr.LocalFragment (.loadCell (.var 0)) := by intro fragment; cases fragment
  exact ⟨.apply (.lambda .var) .unit, skipped_not_local lambdaOutside,
    skipped_not_local callOutside, skipped_not_local cellOutside, rfl, rfl, rfl⟩

theorem equal_final_values_and_stores_do_not_identify_suspended_states
    (returned inserted : Value) (tail : Environment) (store : Store) :
    runStateful 0 (State.initial (.var 0) (returned :: tail) store) =
      .outOfFuel (State.initial (.var 0) (returned :: tail) store) ∧
    runStateful 0 (State.initial ((Expr.var 0).weakenAt 0) (inserted :: returned :: tail) store) =
      .outOfFuel (State.initial (.var 1) (inserted :: returned :: tail) store) ∧
    runStateful 0 (State.initial (.var 0) (returned :: tail) store) ≠
      runStateful 0 (State.initial ((Expr.var 0).weakenAt 0) (inserted :: returned :: tail) store) ∧
    runStateful 1 (State.initial (.var 0) (returned :: tail) store) = .done returned store ∧
    runStateful 1 (State.initial ((Expr.var 0).weakenAt 0) (inserted :: returned :: tail) store) =
      .done returned store := by
  rw [weakenedVar]
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  intro same
  cases same

end Tests.CoreLocalFragmentInsertionBoundary
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentInsertionProperties
/-! Exact values and stores survive insertion for the independent local syntax
fragment. Existing closures and references are opaque returned values, not calls
or allocations, and retained binder indices remain distinct from shifted inputs. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentInsertion

open Solcore Solcore.Core

private def arithmetic (cutoff : Nat) : Expr :=
  .unary .wordNot (.binary .wordSub (.var cutoff) (.var (cutoff + 1)))
private theorem arithmeticLocal (cutoff : Nat) : Expr.LocalFragment (arithmetic cutoff) :=
  .unary (.binary .var .var)
private theorem arithmeticEvaluates (leading suffix : Environment) (left right : Word) (store : Store) :
    Evaluates (leading ++ .word left :: .word right :: suffix) store (arithmetic leading.length)
      (.word (left.sub right).bitNot) store := by
  have leftFound : (leading ++ .word left :: .word right :: suffix)[leading.length]? = some (.word left) := by
    simp
  have rightFound : (leading ++ .word left :: .word right :: suffix)[leading.length + 1]? = some (.word right) := by
    simp
  exact .unary (.binary (.var leftFound) (.var rightFound) rfl) rfl

private def nested : Expr := .letE (.var 1) (.letE (.var 0) (.var 2))
private def nestedShifted : Expr := .letE (.var 2) (.letE (.var 0) (.var 2))
private theorem nestedLocal : Expr.LocalFragment nested := .letE .var (.letE .var .var)
private theorem nestedEvaluates (retained bound : Value) (suffix : Environment) (store : Store) :
    Evaluates (retained :: bound :: suffix) store nested retained store :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))

private def conditional (choice : Bool) : Expr := .ifE (.bool choice) (.var 0) (.var 1)
private theorem conditionalLocal (choice : Bool) : Expr.LocalFragment (conditional choice) := .ifE .bool .var .var
private theorem conditionalEvaluates (choice : Bool) (left right : Value) (suffix : Environment) (store : Store) :
    Evaluates (left :: right :: suffix) store (conditional choice) (if choice then left else right) store := by
  cases choice
  · exact .ifFalse .bool (.var rfl)
  · exact .ifTrue .bool (.var rfl)

private def skippedBadOperand : Expr := .ifE (.bool true) (.var 0) (.binary .wordSub (.bool true) .unit)
private theorem skippedLocal : Expr.LocalFragment skippedBadOperand := .ifE .bool .var (.binary .bool .unit)
private theorem skippedEvaluates (value : Value) (suffix : Environment) (store : Store) :
    Evaluates (value :: suffix) store skippedBadOperand value store := .ifTrue .bool (.var rfl)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LocalInsertion", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def named : Resolved.Expr := .wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) (.var (ident 1))
private def ordered : Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem orderedLowered : Resolved.Lowers [ident 0, ident 1] named ordered := by
  have lowerLeft : Resolved.Lowers [ident 0, ident 1] (.var (ident 0)) (.var 0) := .var .head
  have lowerRight : Resolved.Lowers [ident 0, ident 1] (.var (ident 1)) (.var 1) := .var (.tail (by decide) .head)
  simpa [named, ordered, Expr.wordLt_expansion, Expr.weakenAt] using
    lowerLeft.wordLtWithIds (leftId := ident 2) (rightId := ident 0) lowerRight (by decide) (by decide)
private theorem orderedEvaluates (left right : Word) (store : Store) :
    Evaluates [.word left, .word right] store ordered (.bool (decide (left < right))) store :=
  .letE (.var rfl) (.letE (.var rfl) (.binary (.var rfl) (.var rfl) rfl))

theorem all_three_constant_forms_keep_values_under_arbitrary_retained_prefixes
    (leading suffix : Environment) (inserted : Value) (choice : Bool) (word : Word) (store : Store) :
    Evaluates (leading ++ inserted :: suffix) store .unit .unit store ∧
    Evaluates (leading ++ inserted :: suffix) store (.bool choice) (.bool choice) store ∧
    Evaluates (leading ++ inserted :: suffix) store (.word word) (.word word) store := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.unit.evaluates_insert_iff leading suffix inserted).mpr
      (show Evaluates (leading ++ suffix) store .unit .unit store from .unit)
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.bool.evaluates_insert_iff leading suffix inserted).mpr
      (show Evaluates (leading ++ suffix) store (.bool choice) (.bool choice) store from .bool)
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.word.evaluates_insert_iff leading suffix inserted).mpr
      (show Evaluates (leading ++ suffix) store (.word word) (.word word) store from .word)

theorem arbitrary_suffix_values_are_shifted_past_insertion_at_any_prefix_length
    (leading suffix : Environment) (value inserted : Value) (store : Store) :
    Evaluates (leading ++ value :: suffix) store (.var leading.length) value store ∧
    Evaluates (leading ++ inserted :: value :: suffix) store (.var (leading.length + 1)) value store ∧
    (Expr.var leading.length).LocalFragment ∧
    ((Expr.var leading.length).weakenAt leading.length).LocalFragment := by
  have original : Evaluates (leading ++ value :: suffix) store (.var leading.length) value store := .var (by simp)
  have fragment : (Expr.var leading.length).LocalFragment := .var
  have shifted := (fragment.evaluates_insert_iff leading (value :: suffix) inserted).mpr original
  refine ⟨original, ?_, fragment, fragment.weakenAt leading.length⟩
  simpa only [Expr.weakenAt, Nat.le_refl, ↓reduceIte] using shifted

theorem arbitrary_return_values_have_exact_empty_prefix_preservation_and_reflection
    (environment : Environment) (value inserted : Value) (store : Store) :
    Evaluates (inserted :: value :: environment) store (.var 1) value store ∧
    Evaluates (value :: environment) store (.var 0) value store ∧
    (Evaluates (inserted :: value :: environment) store (.var 1) value store ↔
      Evaluates (value :: environment) store (.var 0) value store) := by
  have original : Evaluates (value :: environment) store (.var 0) value store := .var rfl
  have shifted := original.weakenAt_zero_localFragment .var inserted
  refine ⟨?_, shifted.reflect_weakenAt_zero_localFragment .var, ?_⟩
  · simpa [Expr.weakenAt] using shifted
  · simpa [Expr.weakenAt] using (Expr.LocalFragment.var (index := 0)).evaluates_weaken_zero_iff
      (value :: environment) inserted (initialStore := store) (finalStore := store) (value := value)

theorem existing_cells_and_closures_are_returned_opaquely_without_allocation_or_capture
    (inserted : Value) (environment captured : Environment) (store : Store) (body : Expr) :
    Evaluates (inserted :: .cellRef .word 40 :: environment) [] (.var 1) (.cellRef .word 40) [] ∧
    Evaluates (inserted :: .closure .word .bool body captured :: environment) store (.var 1)
      (.closure .word .bool body captured) store :=
  ⟨(arbitrary_return_values_have_exact_empty_prefix_preservation_and_reflection
      environment (.cellRef .word 40) inserted []).1,
    (arbitrary_return_values_have_exact_empty_prefix_preservation_and_reflection
      environment (.closure .word .bool body captured) inserted store).1⟩

theorem unary_and_binary_primitives_preserve_ordered_words_at_arbitrary_cutoffs
    (leading suffix : Environment) (left right : Word) (inserted : Value) (store : Store) :
    (arithmetic leading.length).LocalFragment ∧
    Evaluates (leading ++ .word left :: .word right :: suffix) store (arithmetic leading.length)
      (.word (left.sub right).bitNot) store ∧
    Evaluates (leading ++ inserted :: .word left :: .word right :: suffix) store
      ((arithmetic leading.length).weakenAt leading.length) (.word (left.sub right).bitNot) store :=
  ⟨arithmeticLocal leading.length, arithmeticEvaluates leading suffix left right store,
    ((arithmeticLocal leading.length).evaluates_insert_iff leading (.word left :: .word right :: suffix) inserted).mpr
      (arithmeticEvaluates leading suffix left right store)⟩

theorem nested_lets_retain_bound_indices_while_shifting_the_original_suffix
    (retained bound inserted : Value) (suffix : Environment) (store : Store) :
    nested.weakenAt 1 = nestedShifted ∧ nestedShifted.LocalFragment ∧
    Evaluates (retained :: bound :: suffix) store nested retained store ∧
    Evaluates (retained :: inserted :: bound :: suffix) store nestedShifted retained store := by
  have same : nested.weakenAt 1 = nestedShifted := by simp [nested, nestedShifted, Expr.weakenAt]
  refine ⟨same, same ▸ nestedLocal.weakenAt 1, nestedEvaluates retained bound suffix store, ?_⟩
  have shifted := (nestedLocal.evaluates_insert_iff [retained] (bound :: suffix) inserted).mpr
    (nestedEvaluates retained bound suffix store)
  simpa only [List.length_cons, List.length_nil, same, List.cons_append, List.nil_append] using shifted

theorem both_conditional_paths_preserve_the_selected_actual_value
    (choice : Bool) (left right inserted : Value) (suffix : Environment) (store : Store) :
    (conditional choice).LocalFragment ∧
    Evaluates (left :: right :: suffix) store (conditional choice) (if choice then left else right) store ∧
    Evaluates (inserted :: left :: right :: suffix) store ((conditional choice).weakenAt 0)
      (if choice then left else right) store :=
  ⟨conditionalLocal choice, conditionalEvaluates choice left right suffix store,
    (conditionalEvaluates choice left right suffix store).weakenAt_zero_localFragment (conditionalLocal choice) inserted⟩

theorem whole_fragment_membership_does_not_require_the_skipped_primitive_to_typecheck
    (value inserted : Value) (suffix : Environment) (store : Store) :
    skippedBadOperand.LocalFragment ∧
    Evaluates (value :: suffix) store skippedBadOperand value store ∧
    Evaluates (inserted :: value :: suffix) store (skippedBadOperand.weakenAt 0) value store :=
  ⟨skippedLocal, skippedEvaluates value suffix store,
    (skippedEvaluates value suffix store).weakenAt_zero_localFragment skippedLocal inserted⟩

theorem resolved_ordered_comparison_lowers_into_the_independent_core_fragment
    (left right : Word) (inserted : Value) (store : Store) :
    Resolved.Lowers [ident 0, ident 1] named ordered ∧ ordered.LocalFragment ∧
    (ordered.weakenAt 0).LocalFragment ∧
    Evaluates [.word left, .word right] (.unit :: store) ordered (.bool (decide (left < right))) (.unit :: store) ∧
    Evaluates [inserted, .word left, .word right] (.unit :: store) (ordered.weakenAt 0)
      (.bool (decide (left < right))) (.unit :: store) :=
  ⟨orderedLowered, orderedLowered.localFragment, orderedLowered.localFragment.weakenAt 0,
    orderedEvaluates left right (.unit :: store),
    (orderedEvaluates left right (.unit :: store)).weakenAt_zero_localFragment orderedLowered.localFragment inserted⟩

end Tests.CoreLocalFragmentInsertion
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentPairBoundary
/-! Independent ordered pair certificates, explicit checkpoints and mathematical
thresholds. Insertion preserves endpoints, not captured machine environments. -/
set_option autoImplicit false
namespace Tests
open Solcore.Core

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def w (n : Nat) : Value := .word (Word.ofNatModulo n)
private def stores : List Store := [[], [.cellRef .word 40, .bool true, w 91]]
private structure Certificate (environment : Environment) (store : Store) where
  expr : Expr
  value : Value
  cost : Nat
  fragment : expr.LocalFragment
  evaluation : Evaluates environment store expr value store
  paths : ∀ continuation, Steps cost ⟨.eval expr environment, continuation, store⟩ ⟨.ret value, continuation, store⟩
private def reference (environment : Environment) (store : Store) (index : Nat) (value : Value)
    (found : environment[index]? = some value) : Certificate environment store :=
  ⟨.var index, value, 1, .var, .var found, fun _ => .cons (.var found) .refl⟩
private def pair {environment : Environment} {store : Store}
    (left right : Certificate environment store) : Certificate environment store where
  expr := .pair left.expr right.expr
  value := .pair left.value right.value
  cost := left.cost + right.cost + 3
  fragment := .pair left.fragment right.fragment
  evaluation := .pair left.evaluation right.evaluation
  paths := by
    intro continuation
    have enter : Steps 1 ⟨.eval (.pair left.expr right.expr) environment, continuation, store⟩
        ⟨.eval left.expr environment, .pairRight right.expr environment :: continuation, store⟩ := .cons .enterPair .refl
    have next : Steps 1 ⟨.ret left.value, .pairRight right.expr environment :: continuation, store⟩
        ⟨.eval right.expr environment, .pairApply left.value :: continuation, store⟩ := .cons .enterPairRight .refl
    have finish : Steps 1 ⟨.ret right.value, .pairApply left.value :: continuation, store⟩
        ⟨.ret (.pair left.value right.value), continuation, store⟩ := .cons .applyPair .refl
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      enter.trans ((left.paths _).trans (next.trans ((right.paths _).trans finish)))
private def binding {environment : Environment} {store : Store} (initializer : Certificate environment store)
    (body : Certificate (initializer.value :: environment) store) : Certificate environment store where
  expr := .letE initializer.expr body.expr
  value := body.value
  cost := initializer.cost + body.cost + 2
  fragment := .letE initializer.fragment body.fragment
  evaluation := .letE initializer.evaluation body.evaluation
  paths := by
    intro continuation
    have enter : Steps 1 ⟨.eval (.letE initializer.expr body.expr) environment, continuation, store⟩
        ⟨.eval initializer.expr environment, .letBody body.expr environment :: continuation, store⟩ := .cons .enterLet .refl
    have next : Steps 1 ⟨.ret initializer.value, .letBody body.expr environment :: continuation, store⟩
        ⟨.eval body.expr (initializer.value :: environment), continuation, store⟩ := .cons .bindLet .refl
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      enter.trans ((initializer.paths _).trans (next.trans (body.paths _)))
private def observe (result : StatefulRunResult) (remaining budget : Nat) (value : Value) (store : Store) : Bool :=
  match result with
  | .done actual final => decide (remaining ≤ budget ∧ actual = value ∧ final = store)
  | .outOfFuel checkpoint => decide (budget < remaining ∧ checkpoint.store = store)
  | .fault _ _ => false
private def execute (start : State) (value : Value) (store : Store) (cost : Nat)
    (path : Steps cost start (.final value store)) : IO Unit := do
  for fuel in List.range (cost + 3) do
    have _ := path.runStateful_done_iff (fuel := fuel)
    have _ := path.runStateful_outOfFuel_iff (fuel := fuel)
    assertTrue (observe (runStateful fuel start) cost fuel value store) "independent exact threshold/value/own store changed"
  for spent in List.range cost do
    match exhausted : runStateful spent start with
    | .outOfFuel checkpoint =>
        have _ := path.residual_of_outOfFuel exhausted
        for additional in List.range (cost - spent + 3) do
          have _ := runStateful_resume exhausted additional
          have _ := path.resumed_done_iff (additional := additional) exhausted
          have _ := path.resumed_outOfFuel_iff (additional := additional) exhausted
          assertTrue (observe (runStateful additional checkpoint) (cost - spent) additional value store)
            "genuine residual cost or own-store result changed"
        if 1 < cost - spent then
          match second : runStateful 1 checkpoint with
          | .outOfFuel next =>
              have _ := runStateful_resume second (cost - spent - 1)
              assertTrue (decide (runStateful (cost - spent - 1) next = .done value store)) "three-chunk completion lost its actual state"
          | _ => throw (IO.userError "second genuine checkpoint missing")
        if 0 < spent then
          assertTrue (match runStateful (cost - spent) start with | .outOfFuel _ => true | _ => false)
            "restart impersonated exact checkpoint resumption"
    | _ => throw (IO.userError "known terminating path lost a genuine checkpoint")
private def exercise (leading suffix : Environment) (inserted : Value) (store : Store)
    (certificate : Certificate (leading ++ suffix) store) (expectedCore : Expr) (expected : Value) (cost : Nat) : IO Unit := do
  assertTrue (decide (certificate.value = expected ∧ certificate.cost = cost ∧
    certificate.expr.weakenAt leading.length = expectedCore)) "independent Core/value/cost certificate changed"
  have _ := certificate.fragment.weakenAt leading.length
  have shiftedEval := (certificate.fragment.evaluates_insert_iff leading suffix inserted).mpr certificate.evaluation
  have _ := (certificate.fragment.evaluates_insert_iff leading suffix inserted).mp shiftedEval
  have _ := certificate.fragment.insertion_paths leading suffix inserted certificate.evaluation
  have shifted := certificate.fragment.steps_insert leading suffix inserted (certificate.paths []) []
  have _ := (certificate.fragment.steps_insert_iff leading suffix inserted).mp shifted
  have _ := (certificate.fragment.steps_insert_iff leading suffix inserted).mpr (certificate.paths [])
  if agrees : certificate.value = expected ∧ certificate.cost = cost then
    execute (.initial certificate.expr (leading ++ suffix) store) expected store cost
      (by simpa only [State.initial, State.final, agrees.1, agrees.2] using certificate.paths [])
    execute (.initial (certificate.expr.weakenAt leading.length) (leading ++ inserted :: suffix) store)
      expected store cost (by simpa only [State.initial, State.final, agrees.1, agrees.2] using shifted)
  else throw (IO.userError "independent value/cost evidence missing")
  for continuation in [[], [.unaryApply .wordNot], [.letBody (.var 0) [w 99]], [.firstApply]] do
    have _ := certificate.fragment.steps_insert leading suffix inserted (certificate.paths []) continuation
    have _ := certificate.fragment.steps_reflect_insert leading suffix inserted shifted continuation
    for (expr, environment) in [(certificate.expr, leading ++ suffix),
        (certificate.expr.weakenAt leading.length, leading ++ inserted :: suffix)] do
      let state : State := ⟨.eval expr environment, continuation, store⟩
      match continuation with
      | [.unaryApply .wordNot] =>
          assertTrue (decide (runStateful cost state = .fault (.invalidUnaryOperand .wordNot expected)
            ⟨.ret expected, continuation, store⟩)) "retained endpoint promised completion or unconditional exhaustion"
      | [.letBody (.var 0) _] =>
          assertTrue (decide (runStateful cost state = .outOfFuel ⟨.ret expected, continuation, store⟩ ∧
            runStateful (cost + 2) state = .done expected store)) "pending safe let frame was silently executed"
      | _ => pure ()
private def pairCheckpoints (x y inserted : Value) (store : Store) : IO Unit := do
  let original := State.initial (.pair (.var 0) (.var 1)) [x, y] store
  let shifted := State.initial (.pair (.var 1) (.var 2)) [inserted, x, y] store
  for (start, environment, leftIndex, rightIndex) in [(original, [x, y], 0, 1), (shifted, [inserted, x, y], 1, 2)] do
    assertTrue (decide (runStateful 1 start = .outOfFuel ⟨.eval (.var leftIndex) environment,
      [.pairRight (.var rightIndex) environment], store⟩)) "pair left entry or saved original environment changed"
    assertTrue (decide (runStateful 2 start = .outOfFuel ⟨.ret x, [.pairRight (.var rightIndex) environment], store⟩ ∧
      runStateful 3 start = .outOfFuel ⟨.eval (.var rightIndex) environment, [.pairApply x], store⟩ ∧
      runStateful 4 start = .outOfFuel ⟨.ret y, [.pairApply x], store⟩ ∧
      runStateful 5 start = .done (.pair x y) store)) "left-to-right pair frames or actual components changed"
    let localLeft := State.initial (.pair (.letE (.var leftIndex) (.var 0)) (.var rightIndex)) environment store
    assertTrue (decide (runStateful 4 localLeft = .outOfFuel
      ⟨.eval (.var 0) (x :: environment), [.pairRight (.var rightIndex) environment], store⟩ ∧
      runStateful 6 localLeft = .outOfFuel ⟨.eval (.var rightIndex) environment, [.pairApply x], store⟩ ∧
      runStateful 8 localLeft = .done (.pair x y) store)) "left-local binding leaked into the right operand's saved environment"
  assertTrue (decide (runStateful 2 original ≠ runStateful 2 shifted)) "own pairRight frames were equated across insertion"
private theorem nominalTyping (left right inserted : Ty) (definitions : DataEnvironment) :
    HasType [left, inserted, right] (.pair (.var 0) (.var 2)) (.product left right) definitions := by
  have fragment : (Expr.pair (.var 0) (.var 1)).LocalFragment := .pair .var .var
  have original : HasType [left, right] (.pair (.var 0) (.var 1)) (.product left right) definitions := .pair (.var rfl) (.var rfl)
  simpa [Expr.weakenAt] using (fragment.hasType_insert_iff [left] [right] inserted).mpr original
private def typingCases : IO Unit := do
  let fragment : (Expr.pair (.var 0) (.var 1)).LocalFragment := .pair .var .var
  for left in [Ty.word, .namedData ⟨91⟩, .function (.namedData ⟨999⟩) .unit] do
    for right in [Ty.bool, .namedData ⟨92⟩] do
      for definitions in [([] : DataEnvironment), [⟨[.namedData ⟨999⟩]⟩]] do
        have typed := nominalTyping left right (.namedData ⟨1000⟩) definitions
        have _ := (fragment.hasType_insert_iff [left] [right] (.namedData ⟨1000⟩)).mp (by simpa [Expr.weakenAt] using typed)
        have _ := fragment.infer_insert [left] [right] (.namedData ⟨1000⟩) definitions
        have original : HasType [left, right] (.pair (.var 0) (.var 1)) (.product left right) definitions := .pair (.var rfl) (.var rfl)
        have zero := original.weakenAt_zero_localFragment fragment .unit
        have _ := zero.reflect_weakenAt_zero_localFragment fragment
        have _ := (fragment.hasType_weaken_zero_iff [left, right] .unit).mp zero
        have _ := fragment.infer_weaken_zero [left, right] .unit definitions
        assertTrue (decide (infer? [left, .namedData ⟨1000⟩, right] (.pair (.var 0) (.var 2)) definitions =
          some (.product left right))) "nominal open typing acquired an inhabitant or data-WF premise"
private def invalidCases (store : Store) : IO Unit := do
  have _ : ¬ (Expr.pair .unit (.lambda .word .word (.var 0))).LocalFragment := by intro h; cases h with | pair _ bad => cases bad
  have _ : ¬ (Expr.pair (.apply (.var 0) .unit) .unit).LocalFragment := by intro h; cases h with | pair bad _ => cases bad
  have _ : ¬ (Expr.pair .unit (.loadCell (.var 0))).LocalFragment := by intro h; cases h with | pair _ bad => cases bad
  have _ : ¬ (Expr.pair (.first (.pair .unit .unit)) .unit).LocalFragment := by intro h; cases h with | pair bad _ => cases bad
  have _ : ¬ (Expr.ifE (.bool true) (.pair .unit .unit) (.pair .unit (.second (.pair .unit .unit)))).LocalFragment := by
    intro h; cases h with | ifE _ _ bad => cases bad with | pair _ bad => cases bad
  let unselected : Expr := .ifE (.bool true) (.pair .unit .unit) (.pair .unit (.second (.pair .unit .unit)))
  have _ : HasType [] unselected (.product .unit .unit) := .ifE .bool (.pair .unit .unit) (.pair .unit (.second (.pair .unit .unit)))
  have _ : Evaluates [] store unselected (.pair .unit .unit) store := .ifTrue .bool (.pair .unit .unit)
  assertTrue (decide (runStateful 8 (.initial unselected [] store) = .done (.pair .unit .unit) store))
    "unselected nonlocal child was confused with failed actual execution"
  let missing : Expr := .pair (.word (Word.ofNatModulo 9)) (.var 0)
  let missingFragment : missing.LocalFragment := .pair .word .var
  have _ := missingFragment.evaluates_insert_iff (initialStore := store) (finalStore := store) (value := .pair (w 9) .unit) [] [] (.cellRef .word 999)
  have _ := missingFragment.infer_insert [] [] (.cell .word)
  assertTrue (decide (infer? [] missing = none ∧ infer? [.cell .word] (missing.weakenAt 0) = none)) "inserted value filled an original missing reference"
  for (expr, env, index) in [(missing, ([] : Environment), 0), (missing.weakenAt 0, [.cellRef .word 999], 1)] do
    assertTrue (decide (runStateful 3 (.initial expr env store) = .fault (.unboundVariable index)
      ⟨.eval (.var index) env, [.pairApply (w 9)], store⟩)) "missing right child lost actual index or left value"
  let wrong : Expr := .unary .wordNot (.bool true)
  let wrongFragment : (Expr.pair wrong (.var 99)).LocalFragment := .pair (.unary .bool) .var
  have _ := wrongFragment.infer_insert [] [] .unit
  for (env, index) in [(([] : Environment), 99), ([Value.unit], 100)] do
    assertTrue (decide (runStateful 3 (.initial (.pair wrong (.var index)) env store) =
      .fault (.invalidUnaryOperand .wordNot (.bool true))
        ⟨.ret (.bool true), [.unaryApply .wordNot, .pairRight (.var index) env], store⟩)) "right failure overtook the wrong left operand"
    assertTrue (decide (runStateful 5 (.initial (.pair (.word (Word.ofNatModulo 9)) wrong) env store) =
      .fault (.invalidUnaryOperand .wordNot (.bool true))
        ⟨.ret (.bool true), [.unaryApply .wordNot, .pairApply (w 9)], store⟩)) "wrong right operand lost its evaluated left component"
  for (env, index) in [(([] : Environment), 0), ([Value.unit], 1)] do
    assertTrue (decide (runStateful 1 (.initial (.pair (.var index) wrong) env store) =
      .fault (.unboundVariable index) ⟨.eval (.var index) env, [.pairRight wrong env], store⟩))
      "missing left reference evaluated the wrong right primitive first"

def coreLocalFragmentPairBoundaryTests : IO Unit := do
  typingCases
  for store in stores do
    invalidCases store
    for (x, y) in [(w 9, w 2), (.cellRef .word 999, .closure .word .bool (.var 80) []),
        (.constructed ⟨⟨91⟩, 4⟩ (.pair .unit (w 7)), .unit)] do
      for inserted in [Value.bool false, .cellRef (.namedData ⟨777⟩) 500] do
        let first := reference [x, y] store 0 x rfl
        let second := reference [x, y] store 1 y rfl
        let simple := pair first second
        exercise [] [x, y] inserted store simple (.pair (.var 1) (.var 2)) (.pair x y) 5
        exercise [x] [y] inserted store simple (.pair (.var 0) (.var 2)) (.pair x y) 5
        exercise [x, y] [] inserted store simple (.pair (.var 0) (.var 1)) (.pair x y) 5
        let nested := pair first (pair second first)
        exercise [] [x, y] inserted store nested (.pair (.var 1) (.pair (.var 2) (.var 1))) (.pair x (.pair y x)) 9
        let localLeft := binding first (reference [x, x, y] store 0 x rfl)
        exercise [] [x, y] inserted store (pair localLeft second)
          (.pair (.letE (.var 1) (.var 0)) (.var 2)) (.pair x y) 8
        let tail := pair (reference [simple.value, x, y] store 0 simple.value rfl) (reference [simple.value, x, y] store 2 y rfl)
        exercise [] [x, y] inserted store (binding simple tail)
          (.letE (.pair (.var 1) (.var 2)) (.pair (.var 0) (.var 3))) (.pair (.pair x y) y) 12
        let retained := pair (reference [.bool true, .unit, x, y] store 0 (.bool true) rfl)
          (pair (reference [.bool true, .unit, x, y] store 2 x rfl) (reference [.bool true, .unit, x, y] store 3 y rfl))
        exercise [.bool true, .unit] [x, y] inserted store retained
          (.pair (.var 0) (.pair (.var 3) (.var 4))) (.pair (.bool true) (.pair x y)) 9
        have shiftedEval := simple.evaluation.weakenAt_zero_localFragment simple.fragment inserted
        have _ := shiftedEval.reflect_weakenAt_zero_localFragment simple.fragment
        have _ := (simple.fragment.evaluates_weaken_zero_iff [x, y] inserted).mp shiftedEval
        have shiftedPath := (simple.paths []).weakenAt_zero_localFragment simple.fragment inserted []
        have _ := shiftedPath.reflect_weakenAt_zero_localFragment simple.fragment []
        pairCheckpoints x y inserted store

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentPairProperties
/-! Independent Core pairs retain original child environments and exact costs.
Static nominal types and arbitrary data definitions never supply runtime values. -/
set_option autoImplicit false
namespace Tests.CoreLocalFragmentPair
open Solcore Solcore.Core

private def nested (index : Nat) : Expr :=
  .pair (.letE (.var index) (.pair (.var 0) (.var (index + 2)))) (.var index)
private theorem nestedLocal (index : Nat) : (nested index).LocalFragment := .pair (.letE .var (.pair .var .var)) .var
private theorem nestedEval (leading suffix : Environment) (left right : Value) (store : Store) :
    Evaluates (leading ++ left :: right :: suffix) store (nested leading.length) (.pair (.pair left right) left) store := by
  have first : (leading ++ left :: right :: suffix)[leading.length]? = some left := by simp
  have second : (left :: (leading ++ left :: right :: suffix))[leading.length + 2]? = some right := by simp
  exact .pair (.letE (.var first) (.pair (.var rfl) (.var second))) (.var first)
private theorem nestedPath (leading suffix : Environment) (left right : Value) (store : Store) :
    Steps 12 (State.initial (nested leading.length) (leading ++ left :: right :: suffix) store)
      (State.final (.pair (.pair left right) left) store) := by
  have first : (leading ++ left :: right :: suffix)[leading.length]? = some left := by simp
  have second : (left :: (leading ++ left :: right :: suffix))[leading.length + 2]? = some right := by simp
  exact .cons .enterPair (.cons .enterLet (.cons (.var first) (.cons .bindLet (.cons .enterPair
    (.cons (.var rfl) (.cons .enterPairRight (.cons (.var second) (.cons .applyPair
    (.cons .enterPairRight (.cons (.var first) (.cons .applyPair .refl)))))))))))
private theorem nestedTyped (leading suffix : Context) (left right : Ty) (definitions : DataEnvironment) :
    HasType (leading ++ left :: right :: suffix) (nested leading.length) (.product (.product left right) left) definitions :=
  .pair (.letE (.var (by simp)) (.pair (.var rfl) (.var (by simp)))) (.var (by simp))

theorem pair_cost_is_the_sum_of_actual_ordered_child_paths_plus_three
    (leading suffix : Environment) (inserted leftValue rightValue : Value) (initialStore middleStore finalStore : Store)
    (left right : Expr) (leftLocal : left.LocalFragment) (rightLocal : right.LocalFragment) (leftCost rightCost : Nat)
    (leftPath : ∀ continuation, Steps leftCost ⟨.eval left (leading ++ suffix), continuation, initialStore⟩ ⟨.ret leftValue, continuation, middleStore⟩)
    (rightPath : ∀ continuation, Steps rightCost ⟨.eval right (leading ++ suffix), continuation, middleStore⟩ ⟨.ret rightValue, continuation, finalStore⟩) :
    Steps (leftCost + rightCost + 3) (State.initial (.pair left right) (leading ++ suffix) initialStore)
      (State.final (.pair leftValue rightValue) finalStore) ∧
    ∀ continuation, Steps (leftCost + rightCost + 3)
      ⟨.eval ((Expr.pair left right).weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
      ⟨.ret (.pair leftValue rightValue), continuation, finalStore⟩ := by
  have path := Steps.cons .enterPair ((leftPath [.pairRight right (leading ++ suffix)]).trans
    (.cons .enterPairRight ((rightPath [.pairApply leftValue]).trans (.cons .applyPair .refl))))
  have exactPath : Steps (leftCost + rightCost + 3) (State.initial (.pair left right) (leading ++ suffix) initialStore)
      (State.final (.pair leftValue rightValue) finalStore) := by simpa [Nat.add_assoc, State.initial, State.final] using path
  exact ⟨exactPath, fun continuation => (Expr.LocalFragment.pair leftLocal rightLocal).steps_insert leading suffix inserted exactPath continuation⟩

theorem nested_pairs_and_lets_weaken_only_original_suffix_positions (cutoff : Nat) :
    (nested cutoff).weakenAt cutoff =
      .pair (.letE (.var (cutoff + 1)) (.pair (.var 0) (.var (cutoff + 3)))) (.var (cutoff + 1)) ∧
    ((nested cutoff).weakenAt cutoff).LocalFragment := by
  exact ⟨by simp [nested, Expr.weakenAt, Nat.add_assoc], (nestedLocal cutoff).weakenAt cutoff⟩

theorem retained_prefix_evaluation_insertion_reflects_the_same_final_store
    (leading suffix : Environment) (left right inserted : Value) (store final : Store) :
    Evaluates (leading ++ inserted :: left :: right :: suffix) store
      ((nested leading.length).weakenAt leading.length) (.pair (.pair left right) left) store ∧
    (Evaluates (leading ++ inserted :: left :: right :: suffix) store
      ((nested leading.length).weakenAt leading.length) (.pair (.pair left right) left) final ↔ final = store) := by
  have shifted := ((nestedLocal leading.length).evaluates_insert_iff leading (left :: right :: suffix) inserted).mpr
    (nestedEval leading suffix left right store)
  refine ⟨shifted, ?_⟩
  constructor
  · intro evaluation
    exact (evaluation_deterministic evaluation shifted).2
  · intro same; subst final; exact shifted

theorem twelve_is_shared_before_choosing_any_outer_continuation
    (leading suffix : Environment) (left right inserted : Value) (store : Store) :
    ∃ cost, cost = 12 ∧ ∀ continuation,
      Steps cost ⟨.eval (nested leading.length) (leading ++ left :: right :: suffix), continuation, store⟩
        ⟨.ret (.pair (.pair left right) left), continuation, store⟩ ∧
      Steps cost ⟨.eval ((nested leading.length).weakenAt leading.length) (leading ++ inserted :: left :: right :: suffix), continuation, store⟩
        ⟨.ret (.pair (.pair left right) left), continuation, store⟩ := by
  obtain ⟨cost, paths⟩ := (nestedLocal leading.length).insertion_paths leading (left :: right :: suffix) inserted (nestedEval leading suffix left right store)
  have same := ((nestedPath leading suffix left right store).final_unique (paths []).1).1
  exact ⟨cost, same.symm, paths⟩

theorem closed_paths_reflect_at_arbitrary_cuts_without_comparing_checkpoint_payloads
    (leading suffix : Environment) (left right inserted result : Value) (store final : Store) (cost : Nat) (continuation : List Frame) :
    Steps 12 ⟨.eval (nested leading.length) (leading ++ left :: right :: suffix), continuation, store⟩
      ⟨.ret (.pair (.pair left right) left), continuation, store⟩ ∧
    (Steps cost (State.initial ((nested leading.length).weakenAt leading.length) (leading ++ inserted :: left :: right :: suffix) store)
      (State.final result final) ↔
      Steps cost (State.initial (nested leading.length) (leading ++ left :: right :: suffix) store) (State.final result final)) := by
  have shifted := (nestedLocal leading.length).steps_insert leading (left :: right :: suffix) inserted
    (nestedPath leading suffix left right store) []
  exact ⟨(nestedLocal leading.length).steps_reflect_insert leading (left :: right :: suffix) inserted shifted continuation,
    (nestedLocal leading.length).steps_insert_iff leading (left :: right :: suffix) inserted⟩

theorem head_insertion_and_reflection_preserve_values_and_unexecuted_outer_frames
    (left right inserted : Value) (suffix : Environment) (store : Store) (continuation : List Frame) :
    Evaluates (inserted :: left :: right :: suffix) store ((nested 0).weakenAt 0) (.pair (.pair left right) left) store ∧
    Evaluates (left :: right :: suffix) store (nested 0) (.pair (.pair left right) left) store ∧
    (Evaluates (inserted :: left :: right :: suffix) store ((nested 0).weakenAt 0) (.pair (.pair left right) left) store ↔
      Evaluates (left :: right :: suffix) store (nested 0) (.pair (.pair left right) left) store) ∧
    Steps 12 ⟨.eval ((nested 0).weakenAt 0) (inserted :: left :: right :: suffix), continuation, store⟩ ⟨.ret (.pair (.pair left right) left), continuation, store⟩ ∧
    Steps 12 ⟨.eval (nested 0) (left :: right :: suffix), continuation, store⟩ ⟨.ret (.pair (.pair left right) left), continuation, store⟩ := by
  have evaluation := (nestedEval [] suffix left right store).weakenAt_zero_localFragment (nestedLocal 0) inserted
  have path := nestedPath [] suffix left right store
  have shifted := path.weakenAt_zero_localFragment (nestedLocal 0) inserted []
  exact ⟨evaluation, evaluation.reflect_weakenAt_zero_localFragment (nestedLocal 0),
    (nestedLocal 0).evaluates_weaken_zero_iff (left :: right :: suffix) inserted,
    path.weakenAt_zero_localFragment (nestedLocal 0) inserted continuation,
    shifted.reflect_weakenAt_zero_localFragment (nestedLocal 0) continuation⟩

theorem arbitrary_static_products_and_data_definitions_survive_retained_insertion
    (leading suffix : Context) (left right inserted : Ty) (definitions : DataEnvironment) :
    HasType (leading ++ inserted :: left :: right :: suffix) ((nested leading.length).weakenAt leading.length)
      (.product (.product left right) left) definitions ∧
    HasType (leading ++ left :: right :: suffix) (nested leading.length) (.product (.product left right) left) definitions ∧
    infer? (leading ++ inserted :: left :: right :: suffix) ((nested leading.length).weakenAt leading.length) definitions =
      some (.product (.product left right) left) := by
  have shifted := ((nestedLocal leading.length).hasType_insert_iff leading (left :: right :: suffix) inserted).mpr (nestedTyped leading suffix left right definitions)
  exact ⟨shifted, ((nestedLocal leading.length).hasType_insert_iff leading (left :: right :: suffix) inserted).mp shifted,
    ((nestedLocal leading.length).infer_insert leading (left :: right :: suffix) inserted definitions).trans
      (infer_complete (nestedTyped leading suffix left right definitions))⟩

theorem static_head_insertion_reflects_exact_types_and_full_inference
    (left right inserted : Ty) (suffix : Context) (definitions : DataEnvironment) :
    HasType (inserted :: left :: right :: suffix) ((nested 0).weakenAt 0) (.product (.product left right) left) definitions ∧
    HasType (left :: right :: suffix) (nested 0) (.product (.product left right) left) definitions ∧
    (HasType (inserted :: left :: right :: suffix) ((nested 0).weakenAt 0) (.product (.product left right) left) definitions ↔
      HasType (left :: right :: suffix) (nested 0) (.product (.product left right) left) definitions) ∧
    infer? (inserted :: left :: right :: suffix) ((nested 0).weakenAt 0) definitions = some (.product (.product left right) left) := by
  have shifted := (nestedTyped [] suffix left right definitions).weakenAt_zero_localFragment (nestedLocal 0) inserted
  exact ⟨shifted, shifted.reflect_weakenAt_zero_localFragment (nestedLocal 0),
    (nestedLocal 0).hasType_weaken_zero_iff (left :: right :: suffix) inserted,
    ((nestedLocal 0).infer_weaken_zero (left :: right :: suffix) inserted definitions).trans
      (infer_complete (nestedTyped [] suffix left right definitions))⟩

theorem nominal_component_types_do_not_provide_runtime_inhabitants (nominal : DataTypeId) (inserted : Ty) :
    infer? [inserted, .namedData nominal, .word] ((nested 0).weakenAt 0) [] =
      some (.product (.product (.namedData nominal) .word) (.namedData nominal)) ∧
    ¬ ∃ value, ValueHasType value (.namedData nominal) := by
  refine ⟨(static_head_insertion_reflects_exact_types_and_full_inference (.namedData nominal) .word inserted [] []).2.2.2, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?] at found

theorem opaque_closures_cells_and_constructed_values_are_only_paired
    (location : Location) (captured : Value) (constructor : ConstructorId) (payload : Value)
    (inserted : Value) (store : Store) (continuation : List Frame) :
    Steps 12 ⟨.eval ((nested 0).weakenAt 0)
      [inserted, .closure .word .bool (.var 99) [captured], .pair (.cellRef .word location) (.constructed constructor payload)], continuation, store⟩
      ⟨.ret (.pair (.pair (.closure .word .bool (.var 99) [captured]) (.pair (.cellRef .word location) (.constructed constructor payload)))
        (.closure .word .bool (.var 99) [captured])), continuation, store⟩ :=
  (nestedPath [] [] _ _ store).weakenAt_zero_localFragment (nestedLocal 0) inserted continuation

private def missing (index : Nat) : Expr := .pair .unit (.var index)
private theorem missingLocal (index : Nat) : (missing index).LocalFragment := .pair .unit .var
theorem missing_pair_children_remain_missing_after_insertion
    (leading suffix : Environment) (inserted : Value) (store : Store) :
    ¬ ∃ result final, Evaluates (leading ++ inserted :: suffix) store
      ((missing (leading.length + suffix.length)).weakenAt leading.length) result final := by
  rintro ⟨result, final, path⟩
  have original := ((missingLocal (leading.length + suffix.length)).evaluates_insert_iff leading suffix inserted).mp path
  cases original with
  | pair _ right =>
    cases right with
    | var found => simp only [← List.length_append] at found; simp at found
theorem missing_pair_inference_is_full_none_for_arbitrary_definitions
    (leading suffix : Context) (inserted : Ty) (definitions : DataEnvironment) :
    infer? (leading ++ inserted :: suffix) ((missing (leading.length + suffix.length)).weakenAt leading.length) definitions = none := by
  rw [(missingLocal (leading.length + suffix.length)).infer_insert leading suffix inserted definitions]
  cases accepted : infer? (leading ++ suffix) (missing (leading.length + suffix.length)) definitions with
  | none => rfl
  | some type =>
    have typed := infer_sound accepted
    cases typed with
    | pair _ right =>
      cases right with
      | var found => simp only [← List.length_append] at found; simp at found

private def wrong : Expr := .pair .unit (.unary .wordNot (.bool true))
private theorem wrongLocal : wrong.LocalFragment := .pair .unit (.unary .bool)
theorem structural_pair_membership_does_not_license_wrong_primitive_children
    (leading suffix : Environment) (inserted : Value) (store : Store) (context : Context) (insertedType : Ty) (definitions : DataEnvironment) :
    wrong.LocalFragment ∧ infer? (insertedType :: context) (wrong.weakenAt 0) definitions = none ∧
    ¬ ∃ result final, Evaluates (leading ++ inserted :: suffix) store (wrong.weakenAt leading.length) result final := by
  refine ⟨wrongLocal, (wrongLocal.infer_weaken_zero context insertedType definitions).trans (by rfl), ?_⟩
  rintro ⟨result, final, path⟩
  have original := (wrongLocal.evaluates_insert_iff leading suffix inserted).mp path
  cases original with
  | pair _ right =>
    cases right with
    | unary operand applied => cases operand; cases applied

end Tests.CoreLocalFragmentPair
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentTermination
/-! Local termination does not require a typed store or terminating closures
in the environment. Returning those values does not execute or dereference them. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentTermination

open Solcore.Core

private def returnedPair : Expr :=
  .letE (.var 0) (.ifE (.bool true) (.pair (.var 0) (.var 2)) (.pair (.var 1) (.var 2)))

private theorem returnedPair_fragment : returnedPair.LocalFragment :=
  .letE .var (.ifE .bool (.pair .var .var) (.pair .var .var))

private theorem returnedPair_typed (parameterType resultType : Ty) :
    HasType [.cell .word, .function parameterType resultType] returnedPair
      (.product (.cell .word) (.function parameterType resultType)) :=
  .letE (.var rfl) (.ifE .bool (.pair (.var rfl) (.var rfl)) (.pair (.var rfl) (.var rfl)))

/-- The same arbitrary store is retained while local binding and branching
return an untouched reference and closure supplied by the caller. -/
theorem returning_a_closure_and_reference_needs_no_store_or_termination_premise
    {parameterType resultType : Ty} {body : Expr} {captured : Environment}
    (closureTyped : RuntimeValueHasType [.word]
      (.closure parameterType resultType body captured) (.function parameterType resultType))
    (store : Store) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel
        (.initial returnedPair
          [.cellRef .word 0, .closure parameterType resultType body captured] store) =
        .done (.pair (.cellRef .word 0) (.closure parameterType resultType body captured)) store := by
  have environmentTyped : RuntimeEnvironmentHasTypes [.word]
      [.cellRef .word 0, .closure parameterType resultType body captured]
      [.cell .word, .function parameterType resultType] :=
    .cons (.cellRef rfl) (.cons closureTyped .nil)
  obtain ⟨value, evaluation, _⟩ :=
    returnedPair_fragment.runtime_evaluates (returnedPair_typed parameterType resultType)
      environmentTyped store
  have originalValue : Evaluates
      [.cellRef .word 0, .closure parameterType resultType body captured]
      store returnedPair
      (.pair (.cellRef .word 0) (.closure parameterType resultType body captured)) store :=
    .letE (.var rfl) (.ifTrue .bool (.pair (.var rfl) (.var rfl)))
  obtain ⟨rfl, _⟩ := evaluation_deterministic evaluation originalValue
  exact evaluation_runStateful_complete_with_sufficient_fuel evaluation

/-- Even an absent referenced location is harmless when the expression only
returns the reference. It would not satisfy the full machine's store invariant. -/
theorem returning_reference_from_an_empty_store :
    (¬ StoreHasTypes [.word] []) ∧
      ∃ value, Evaluates [.cellRef .word 0] [] (.var 0) value [] ∧
        RuntimeValueHasType [.word] value (.cell .word) := by
  constructor
  · intro typed
    have sameLength := typed.length_eq
    simp at sameLength
  · exact Expr.LocalFragment.var.runtime_evaluates (.var rfl)
      (.cons (.cellRef rfl) .nil) []

end Tests.CoreLocalFragmentTermination
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentTypingInsertionBoundary
/-! Typing insertion has a real position boundary. Whole structural membership
does not imply typing, even when an unselected ill-typed branch is never run. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentTypingInsertionBoundary

open Solcore.Core

private theorem weakenedBeyond : (Expr.var 0).weakenAt 1 = .var 0 := by simp [Expr.weakenAt]
private def badPrimitive : Expr := .binary .wordAdd (.bool true) (.var 0)
private theorem badFragment : badPrimitive.LocalFragment := .binary .bool .var
private theorem noTypingOfNone {context : Context} {expr : Expr} {definitions : DataEnvironment}
    (rejected : infer? context expr definitions = none) (type : Ty) : ¬HasType context expr type definitions := by
  intro typing
  have inferred := infer_complete typing
  rw [rejected] at inferred
  cases inferred
private theorem inferNoneOfNoTyping {context : Context} {expr : Expr} {definitions : DataEnvironment}
    (rejected : ∀ type, ¬HasType context expr type definitions) : infer? context expr definitions = none := by
  cases inferred : infer? context expr definitions with
  | none => rfl
  | some type => exact False.elim (rejected type (infer_sound inferred))
private theorem missingRejected (definitions : DataEnvironment) : infer? [] (.var 0) definitions = none := by
  apply inferNoneOfNoTyping
  intro type typing
  cases typing with
  | var found => cases found
private theorem badNoTyping {context : Context} {definitions : DataEnvironment} {type : Ty} :
    ¬HasType context badPrimitive type definitions := by
  intro typing
  cases typing with
  | binary left _ => cases left

theorem clamped_out_of_range_insertion_can_enable_an_unshifted_missing_reference
    (definitions : DataEnvironment) :
    Context.insertAt [] 1 .bool = [.bool] ∧ (Expr.var 0).weakenAt 1 = .var 0 ∧
    Expr.LocalFragment (.var 0) ∧
    HasType (Context.insertAt [] 1 .bool) ((Expr.var 0).weakenAt 1) .bool definitions ∧
    ¬HasType [] (.var 0) .bool definitions ∧
    infer? (Context.insertAt [] 1 .bool) ((Expr.var 0).weakenAt 1) definitions = some .bool ∧
    infer? [] (.var 0) definitions = none := by
  have enabled : HasType (Context.insertAt [] 1 .bool) ((Expr.var 0).weakenAt 1) .bool definitions := by
    rw [weakenedBeyond]
    exact .var rfl
  refine ⟨rfl, weakenedBeyond, .var, enabled, ?_, infer_complete enabled, ?_⟩
  · intro typing
    cases typing with
    | var found => cases found
  · exact missingRejected definitions

theorem properly_shifted_missing_references_remain_rejected_without_original_scope
    (inserted resultType : Ty) (definitions : DataEnvironment) :
    Expr.LocalFragment ((Expr.var 0).weakenAt 0) ∧
    ¬HasType [] (.var 0) resultType definitions ∧
    ¬HasType [inserted] ((Expr.var 0).weakenAt 0) resultType definitions ∧
    infer? [] (.var 0) definitions = none ∧
    infer? [inserted] ((Expr.var 0).weakenAt 0) definitions = none := by
  have rejected := missingRejected definitions
  have missing := noTypingOfNone rejected resultType
  refine ⟨Expr.LocalFragment.weakenAt .var 0, missing, ?_, rejected, ?_⟩
  · intro typing
    exact missing (typing.reflect_weakenAt_zero_localFragment .var)
  · exact (Expr.LocalFragment.var.infer_weaken_zero [] inserted definitions).trans rejected

theorem unshifted_lookup_changes_inference_while_correct_insertion_retains_the_old_type
    (old inserted : Ty) (different : inserted ≠ old) (tail : Context) (definitions : DataEnvironment) :
    infer? (old :: tail) (.var 0) definitions = some old ∧
    infer? (inserted :: old :: tail) (.var 0) definitions = some inserted ∧
    infer? (inserted :: old :: tail) ((Expr.var 0).weakenAt 0) definitions = some old ∧
    HasType (inserted :: old :: tail) ((Expr.var 0).weakenAt 0) old definitions ∧
    infer? (old :: tail) (.var 0) definitions ≠
      infer? (inserted :: old :: tail) (.var 0) definitions := by
  have original : HasType (old :: tail) (.var 0) old definitions := .var rfl
  have shifted := original.weakenAt_zero_localFragment .var inserted
  have originalInfer := infer_complete original
  have newInfer : infer? (inserted :: old :: tail) (.var 0) definitions = some inserted :=
    infer_complete (.var rfl)
  refine ⟨originalInfer, newInfer, infer_complete shifted, shifted, ?_⟩
  rw [originalInfer, newInfer]
  intro same
  exact different (Option.some.inj same).symm

theorem wrong_primitive_remains_rejected_at_every_valid_retained_prefix
    (leading suffix : Context) (inserted : Ty) (definitions : DataEnvironment) :
    badPrimitive.LocalFragment ∧
    infer? (leading ++ suffix) badPrimitive definitions = none ∧
    infer? (leading ++ inserted :: suffix) (badPrimitive.weakenAt leading.length) definitions = none ∧
    (∀ type, ¬HasType (leading ++ suffix) badPrimitive type definitions) ∧
    (∀ type, ¬HasType (leading ++ inserted :: suffix)
      (badPrimitive.weakenAt leading.length) type definitions) := by
  have rejected : infer? (leading ++ suffix) badPrimitive definitions = none :=
    inferNoneOfNoTyping (fun _ => badNoTyping)
  refine ⟨badFragment, rejected, (badFragment.infer_insert leading suffix inserted definitions).trans rejected,
    noTypingOfNone rejected, ?_⟩
  intro type typing
  exact noTypingOfNone rejected type ((badFragment.hasType_insert_iff leading suffix inserted).mp typing)

private def skipped (choice : Bool) : Expr :=
  if choice then .ifE (.bool true) .unit badPrimitive else .ifE (.bool false) badPrimitive .unit
private theorem skippedFragment (choice : Bool) : (skipped choice).LocalFragment := by
  cases choice
  · exact .ifE .bool badFragment .unit
  · exact .ifE .bool .unit badFragment

theorem selected_constant_execution_does_not_type_an_unselected_bad_primitive
    (choice : Bool) (context : Context) (inserted : Ty) (definitions : DataEnvironment)
    (environment : Environment) (store : Store) :
    (skipped choice).LocalFragment ∧
    Evaluates environment store (skipped choice) .unit store ∧
    runStateful 4 (State.initial (skipped choice) environment store) = .done .unit store ∧
    infer? context (skipped choice) definitions = none ∧
    infer? (inserted :: context) ((skipped choice).weakenAt 0) definitions = none ∧
    (∀ type, ¬HasType (inserted :: context) ((skipped choice).weakenAt 0) type definitions) := by
  have rejected : infer? context (skipped choice) definitions = none := by
    apply inferNoneOfNoTyping
    intro type typing
    cases choice
    · cases typing with
      | ifE _ branch _ => exact badNoTyping branch
    · cases typing with
      | ifE _ _ branch => exact badNoTyping branch
  have evaluation : Evaluates environment store (skipped choice) .unit store := by
    cases choice
    · exact .ifFalse .bool .unit
    · exact .ifTrue .bool .unit
  have run : runStateful 4 (State.initial (skipped choice) environment store) = .done .unit store := by
    cases choice <;> rfl
  refine ⟨skippedFragment choice, evaluation, run, rejected,
    ((skippedFragment choice).infer_weaken_zero context inserted definitions).trans rejected, ?_⟩
  intro type typing
  exact noTypingOfNone rejected type
    (((skippedFragment choice).hasType_weaken_zero_iff context inserted).mp typing)

theorem selected_branch_does_not_supply_a_type_for_a_missing_unselected_reference
    (inserted : Ty) (definitions : DataEnvironment) (environment : Environment) (store : Store) :
    Expr.LocalFragment (.ifE (.bool true) .unit (.var 0)) ∧
    Evaluates environment store (.ifE (.bool true) .unit (.var 0)) .unit store ∧
    infer? [] (.ifE (.bool true) .unit (.var 0)) definitions = none ∧
    infer? [inserted] ((Expr.ifE (.bool true) .unit (.var 0)).weakenAt 0) definitions = none := by
  have fragment : Expr.LocalFragment (.ifE (.bool true) .unit (.var 0)) := .ifE .bool .unit .var
  have rejected : infer? [] (.ifE (.bool true) .unit (.var 0)) definitions = none := by
    apply inferNoneOfNoTyping
    intro type typing
    cases typing with
    | ifE _ _ branch =>
        cases branch with
        | var found => cases found
  exact ⟨fragment, .ifTrue .bool .unit, rejected, (fragment.infer_weaken_zero [] inserted definitions).trans rejected⟩

end Tests.CoreLocalFragmentTypingInsertionBoundary
end

section
-- leanmerge: from Solcore.Test.CoreLocalFragmentTypingInsertionProperties
/-! Independent local typing remains exact under retained-prefix insertion.
Context types and data definitions are arbitrary; no runtime inhabitants or
allocation assumptions are used to establish static lookup and inference. -/

set_option autoImplicit false

namespace Tests.CoreLocalFragmentTypingInsertion

open Solcore Solcore.Core

private def arithmetic (cutoff : Nat) : Expr :=
  .unary .wordNot (.binary .wordSub (.var cutoff) (.var (cutoff + 1)))
private theorem arithmeticLocal (cutoff : Nat) : Expr.LocalFragment (arithmetic cutoff) :=
  .unary (.binary .var .var)
private theorem arithmeticTyped (leading suffix : Context) (definitions : DataEnvironment) :
    HasType (leading ++ .word :: .word :: suffix) (arithmetic leading.length) .word definitions :=
  .unary (.binary (.var (by simp [BinaryOp.leftType])) (.var (by simp [BinaryOp.rightType, BinaryOp.leftType])))

private def nested : Expr := .letE (.var 1) (.letE (.var 0) (.var 2))
private def nestedShifted : Expr := .letE (.var 2) (.letE (.var 0) (.var 2))
private theorem nestedLocal : Expr.LocalFragment nested := .letE .var (.letE .var .var)
private theorem nestedTyped (retained bound : Ty) (suffix : Context) (definitions : DataEnvironment) :
    HasType (retained :: bound :: suffix) nested retained definitions :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))

private def conditional (choice : Bool) : Expr := .ifE (.bool choice) (.var 0) (.var 1)
private theorem conditionalLocal (choice : Bool) : Expr.LocalFragment (conditional choice) := .ifE .bool .var .var
private theorem conditionalTyped (choice : Bool) (type : Ty) (suffix : Context) (definitions : DataEnvironment) :
    HasType (type :: type :: suffix) (conditional choice) type definitions := .ifE .bool (.var rfl) (.var rfl)

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"LocalTypingInsertion", by decide⟩], by decide⟩⟩, 0⟩
private def ident (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def named : Resolved.Expr := .wordLtWithIds (ident 2) (ident 0) (.var (ident 0)) (.var (ident 1))
private def ordered : Expr := .letE (.var 0) (.letE (.var 2) (.binary .wordGt (.var 0) (.var 1)))
private theorem orderedLowered : Resolved.Lowers [ident 0, ident 1] named ordered := by
  have lowerLeft : Resolved.Lowers [ident 0, ident 1] (.var (ident 0)) (.var 0) := .var .head
  have lowerRight : Resolved.Lowers [ident 0, ident 1] (.var (ident 1)) (.var 1) := .var (.tail (by decide) .head)
  simpa [named, ordered, Expr.wordLt_expansion, Expr.weakenAt] using
    lowerLeft.wordLtWithIds (leftId := ident 2) (rightId := ident 0) lowerRight (by decide) (by decide)
private theorem orderedTyped (definitions : DataEnvironment) : HasType [.word, .word] ordered .bool definitions :=
  .letE (.var rfl) (.letE (.var rfl) (.binary (.var rfl) (.var rfl)))

theorem all_three_constant_forms_retain_types_with_arbitrary_data_definitions
    (leading suffix : Context) (inserted : Ty) (choice : Bool) (word : Word) (definitions : DataEnvironment) :
    HasType (leading ++ inserted :: suffix) .unit .unit definitions ∧
    HasType (leading ++ inserted :: suffix) (.bool choice) .bool definitions ∧
    HasType (leading ++ inserted :: suffix) (.word word) .word definitions := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.unit.hasType_insert_iff leading suffix inserted).mpr
      (show HasType (leading ++ suffix) .unit .unit definitions from .unit)
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.bool.hasType_insert_iff leading suffix inserted).mpr
      (show HasType (leading ++ suffix) (.bool choice) .bool definitions from .bool)
  · simpa only [Expr.weakenAt] using (Expr.LocalFragment.word.hasType_insert_iff leading suffix inserted).mpr
      (show HasType (leading ++ suffix) (.word word) .word definitions from .word)

theorem arbitrary_suffix_types_are_shifted_at_the_retained_prefix_length
    (leading suffix : Context) (type inserted : Ty) (definitions : DataEnvironment) :
    HasType (leading ++ type :: suffix) (.var leading.length) type definitions ∧
    HasType (leading ++ inserted :: type :: suffix) (.var (leading.length + 1)) type definitions ∧
    infer? (leading ++ inserted :: type :: suffix) (.var (leading.length + 1)) definitions = some type := by
  have original : HasType (leading ++ type :: suffix) (.var leading.length) type definitions := .var (by simp)
  have fragment : (Expr.var leading.length).LocalFragment := .var
  have shifted := (fragment.hasType_insert_iff leading (type :: suffix) inserted).mpr original
  refine ⟨original, ?_, ?_⟩
  · simpa only [Expr.weakenAt, Nat.le_refl, ↓reduceIte] using shifted
  · simpa only [Expr.weakenAt, Nat.le_refl, ↓reduceIte] using
      (fragment.infer_insert leading (type :: suffix) inserted definitions).trans (infer_complete original)

theorem head_insertion_has_exact_type_preservation_reflection_and_inference
    (context : Context) (type inserted : Ty) (definitions : DataEnvironment) :
    HasType (inserted :: type :: context) (.var 1) type definitions ∧
    HasType (type :: context) (.var 0) type definitions ∧
    (HasType (inserted :: type :: context) (.var 1) type definitions ↔
      HasType (type :: context) (.var 0) type definitions) ∧
    infer? (inserted :: type :: context) (.var 1) definitions = some type := by
  have original : HasType (type :: context) (.var 0) type definitions := .var rfl
  have fragment : (Expr.var 0).LocalFragment := .var
  have shifted := original.weakenAt_zero_localFragment fragment inserted
  refine ⟨?_, shifted.reflect_weakenAt_zero_localFragment fragment, ?_, ?_⟩
  · simpa [Expr.weakenAt] using shifted
  · simpa [Expr.weakenAt] using fragment.hasType_weaken_zero_iff (type :: context) inserted
      (type := type) (definitions := definitions)
  · simpa [Expr.weakenAt] using
      (fragment.infer_weaken_zero (type :: context) inserted definitions).trans (infer_complete original)

theorem retained_types_before_the_cutoff_keep_their_original_position
    (retained inserted : Ty) (suffix : Context) (definitions : DataEnvironment) :
    (Expr.var 0).weakenAt 1 = .var 0 ∧
    HasType (retained :: inserted :: suffix) (.var 0) retained definitions ∧
    infer? (retained :: inserted :: suffix) (.var 0) definitions = some retained := by
  have original : HasType (retained :: suffix) (.var 0) retained definitions := .var rfl
  have shifted := ((Expr.LocalFragment.var (index := 0)).hasType_insert_iff [retained] suffix inserted).mpr original
  have typed : HasType (retained :: inserted :: suffix) (.var 0) retained definitions := by
    simpa [Expr.weakenAt] using shifted
  exact ⟨by simp [Expr.weakenAt], typed, infer_complete typed⟩

theorem opaque_nominal_context_types_need_no_runtime_inhabitant_or_definition
    (dataType : DataTypeId) (inserted : Ty) (suffix : Context) :
    HasType (inserted :: .namedData dataType :: suffix) (.var 1) (.namedData dataType) [] ∧
    infer? (inserted :: .namedData dataType :: suffix) (.var 1) [] = some (.namedData dataType) := by
  have headResult := head_insertion_has_exact_type_preservation_reflection_and_inference suffix (.namedData dataType) inserted []
  exact ⟨headResult.1, headResult.2.2.2⟩

theorem unary_and_binary_word_primitives_retain_typing_and_whole_inference
    (leading suffix : Context) (inserted : Ty) (definitions : DataEnvironment) :
    (arithmetic leading.length).LocalFragment ∧
    HasType (leading ++ inserted :: .word :: .word :: suffix)
      ((arithmetic leading.length).weakenAt leading.length) .word definitions ∧
    infer? (leading ++ inserted :: .word :: .word :: suffix)
      ((arithmetic leading.length).weakenAt leading.length) definitions = some .word :=
  ⟨arithmeticLocal leading.length,
    ((arithmeticLocal leading.length).hasType_insert_iff leading (.word :: .word :: suffix) inserted).mpr
      (arithmeticTyped leading suffix definitions),
    ((arithmeticLocal leading.length).infer_insert leading (.word :: .word :: suffix) inserted definitions).trans
      (infer_complete (arithmeticTyped leading suffix definitions))⟩

theorem nested_lets_keep_bound_types_while_shifting_only_the_original_suffix
    (retained bound inserted : Ty) (suffix : Context) (definitions : DataEnvironment) :
    nested.weakenAt 1 = nestedShifted ∧ nestedShifted.LocalFragment ∧
    HasType (retained :: inserted :: bound :: suffix) nestedShifted retained definitions ∧
    infer? (retained :: inserted :: bound :: suffix) nestedShifted definitions = some retained := by
  have same : nested.weakenAt 1 = nestedShifted := by simp [nested, nestedShifted, Expr.weakenAt]
  have shifted := (nestedLocal.hasType_insert_iff [retained] (bound :: suffix) inserted).mpr
    (nestedTyped retained bound suffix definitions)
  have typing : HasType (retained :: inserted :: bound :: suffix) nestedShifted retained definitions := by
    simpa only [List.length_cons, List.length_nil, same, List.cons_append, List.nil_append] using shifted
  exact ⟨same, same ▸ nestedLocal.weakenAt 1, typing, infer_complete typing⟩

theorem both_conditional_choices_keep_the_common_branch_type
    (choice : Bool) (type inserted : Ty) (suffix : Context) (definitions : DataEnvironment) :
    (conditional choice).LocalFragment ∧
    HasType (type :: type :: suffix) (conditional choice) type definitions ∧
    HasType (inserted :: type :: type :: suffix) ((conditional choice).weakenAt 0) type definitions ∧
    infer? (inserted :: type :: type :: suffix) ((conditional choice).weakenAt 0) definitions = some type :=
  ⟨conditionalLocal choice, conditionalTyped choice type suffix definitions,
    (conditionalTyped choice type suffix definitions).weakenAt_zero_localFragment (conditionalLocal choice) inserted,
    ((conditionalLocal choice).infer_weaken_zero (type :: type :: suffix) inserted definitions).trans
      (infer_complete (conditionalTyped choice type suffix definitions))⟩

theorem resolved_ordered_comparison_supports_core_only_typing_insertion
    (inserted : Ty) (definitions : DataEnvironment) :
    Resolved.Lowers [ident 0, ident 1] named ordered ∧ ordered.LocalFragment ∧
    HasType [inserted, .word, .word] (ordered.weakenAt 0) .bool definitions ∧
    infer? [inserted, .word, .word] (ordered.weakenAt 0) definitions = some .bool :=
  ⟨orderedLowered, orderedLowered.localFragment,
    (orderedTyped definitions).weakenAt_zero_localFragment orderedLowered.localFragment inserted,
    (orderedLowered.localFragment.infer_weaken_zero [.word, .word] inserted definitions).trans
      (infer_complete (orderedTyped definitions))⟩

end Tests.CoreLocalFragmentTypingInsertion
end

section
-- leanmerge: from Solcore.Test.CoreLocalLoop
/-! Loop helper tests cover actual shared mutation order, transfer propagation,
cyclic administrative cells, finite safety and an all-fuel nonterminating run.
Native Core stores intentionally include the helper's function cell. -/

set_option autoImplicit false

namespace Tests.CoreLocalLoop

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def reason : Word := word 41
private def escaped : Word := word 42

/-- Outer scope is trace reference, then remaining-count reference. -/
private def condition : Expr := LanguageResult.success
  (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (literal 1)))
    (.binary .wordGt (.loadCell (.var 2)) (literal 0)))

private def whileBody : Expr :=
  .letE (.storeCell (.var 1) (.binary .wordSub (.loadCell (.var 1)) (literal 1)))
    (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (literal 10)))
      (LocalLoop.fallthrough .word))

private def continuedBody : Expr := LocalLoop.sequence .word
  (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (literal 10)))
    (LocalLoop.continuing .word))
  (.letE (.storeCell (.var 0) (literal 999)) (LocalLoop.fallthrough .word))

private def post : Expr :=
  .letE (.storeCell (.var 1) (.binary .wordSub (.loadCell (.var 1)) (literal 1)))
    (.letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (literal 100)))
      (LocalLoop.fallthrough .word))

private def program (testCondition body testPost : Expr) : Program := {
  resultType := LanguageResult.resultType .word
  body := .letE (.newCell .word (literal 3))
    (.letE (.newCell .word (literal 0))
      (LocalControl.finish .word
        (LocalControl.sequence .word
          (LocalLoop.toControl .word (LocalLoop.iterate .word testCondition body testPost reason) escaped)
          (LocalControl.returned (.loadCell (.var 0))))
        (LanguageResult.failure .word (.word reason))))
}

private def closure (testCondition body testPost : Expr) : Value :=
  LocalLoop.installedClosure .word testCondition body testPost reason 2
    [.cellRef .word 1, .cellRef .word 0]

private def whileProgram : Program := program condition whileBody (LocalLoop.fallthrough .word)
private def forProgram : Program := program condition continuedBody post

private theorem while_checked : whileProgram.check = true := by
  simp [whileProgram, program, condition, whileBody, LocalLoop.iterate, LocalLoop.loopBody,
    LocalLoop.conditional, LocalLoop.advance, LocalLoop.invoke, LocalLoop.fallthrough,
    LocalLoop.toControl, LocalLoop.resultType, LocalLoop.controlType, LocalLoop.transferType,
    LocalLoop.functionType, LocalLoop.returned, LocalControl.choose, LocalControl.finish,
    LocalControl.sequence, LocalControl.returned, LocalControl.controlType,
    OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  decide

private theorem for_checked : forProgram.check = true := by
  simp [forProgram, program, condition, continuedBody, post, LocalLoop.iterate, LocalLoop.loopBody,
    LocalLoop.sequence, LocalLoop.continuing, LocalLoop.conditional, LocalLoop.advance,
    LocalLoop.invoke, LocalLoop.fallthrough, LocalLoop.toControl, LocalLoop.resultType,
    LocalLoop.controlType, LocalLoop.transferType, LocalLoop.functionType, LocalLoop.returned,
    LocalControl.choose, LocalControl.finish, LocalControl.sequence, LocalControl.returned,
    LocalControl.controlType, OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  decide

set_option maxRecDepth 8192 in
/-- Four conditions and three bodies share the same trace cell: 4 + 3*10. -/
private theorem while_completed : whileProgram.runStateful 1500 =
    .done (.inRight .word (scalar 34))
      [scalar 0, scalar 34, .inRight .unit (closure condition whileBody (LocalLoop.fallthrough .word))] := by
  simp [whileProgram, program, condition, whileBody, closure, LocalLoop.installedClosure,
    LocalLoop.iterate, LocalLoop.loopBody, LocalLoop.conditional, LocalLoop.advance,
    LocalLoop.invoke, LocalLoop.fallthrough, LocalLoop.toControl, LocalLoop.resultType,
    LocalLoop.controlType, LocalLoop.transferType, LocalLoop.functionType, LocalLoop.returned,
    LocalControl.choose, LocalControl.finish, LocalControl.sequence, LocalControl.returned,
    LocalControl.controlType, OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

set_option maxRecDepth 8192 in
/-- Continue skips the body tail, then post runs before the next condition.
The trace records 4 + 3*10 + 3*100, and the counter reaches zero. -/
private theorem for_completed : forProgram.runStateful 2000 =
    .done (.inRight .word (scalar 334))
      [scalar 0, scalar 334, .inRight .unit (closure condition continuedBody post)] := by
  simp [forProgram, program, condition, continuedBody, post, closure, LocalLoop.installedClosure,
    LocalLoop.iterate, LocalLoop.loopBody, LocalLoop.sequence, LocalLoop.continuing,
    LocalLoop.conditional, LocalLoop.advance, LocalLoop.invoke, LocalLoop.fallthrough,
    LocalLoop.toControl, LocalLoop.resultType, LocalLoop.controlType, LocalLoop.transferType,
    LocalLoop.functionType, LocalLoop.returned, LocalControl.choose, LocalControl.finish,
    LocalControl.sequence, LocalControl.returned, LocalControl.controlType,
    OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

example (fuel : Nat) : (whileProgram.runStateful fuel).HasType whileProgram.resultType :=
  Program.checked_runStateful_has_type while_checked fuel

example (fuel : Nat) : (forProgram.runStateful fuel).HasType forProgram.resultType :=
  Program.checked_runStateful_has_type for_checked fuel

example (spent additional : Nat) (checkpoint : State)
    (exhausted : forProgram.runStateful spent = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType forProgram.resultType ∧
      runStateful additional checkpoint = forProgram.runStateful (spent + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound for_checked).bodyHasType) exhausted additional

example : ∃ required, ∀ fuel, required ≤ fuel → forProgram.runStateful fuel =
    .done (.inRight .word (scalar 334))
      [scalar 0, scalar 334, .inRight .unit (closure condition continuedBody post)] :=
  evaluation_runStateful_complete_with_sufficient_fuel (runStateful_evaluation_sound for_completed)

private def spinCondition : Expr := LanguageResult.success (.bool true)
private def spinBody : Expr := LocalLoop.continuing .unit
private def spinPost : Expr := LocalLoop.fallthrough .unit
private def spinProgram : Program := {
  resultType := LocalLoop.resultType .unit
  body := LocalLoop.iterate .unit spinCondition spinBody spinPost reason
}

private def spinState : State := .initial
  (LocalLoop.loopBody .unit spinCondition spinBody spinPost reason)
  [.unit, .cellRef (OptionalCell.cellType (LocalLoop.functionType .unit)) 0]
  [.inRight .unit (LocalLoop.installedClosure .unit spinCondition spinBody spinPost reason 0 [])]

private theorem spin_checked : spinProgram.check = true := by
  simp [spinProgram, spinCondition, spinBody, spinPost, LocalLoop.iterate, LocalLoop.loopBody,
    LocalLoop.conditional, LocalLoop.advance, LocalLoop.invoke, LocalLoop.fallthrough,
    LocalLoop.continuing, LocalLoop.resultType, LocalLoop.controlType, LocalLoop.transferType,
    LocalLoop.functionType, LocalLoop.returned, LocalControl.choose, LocalControl.controlType,
    OptionalCell.allocate, OptionalCell.read, OptionalCell.cellType, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt]
  decide

/-- Tail calls return to the exact same state, store and continuation. -/
private theorem spin_cycle : runStateful 53 spinState = .outOfFuel spinState := by
  simp [spinState, spinCondition, spinBody, spinPost, LocalLoop.installedClosure,
    LocalLoop.loopBody, LocalLoop.conditional, LocalLoop.advance, LocalLoop.invoke,
    LocalLoop.fallthrough, LocalLoop.continuing, LocalLoop.returned, LocalControl.choose,
    OptionalCell.read, LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt]
  rfl

private theorem spin_reached : spinProgram.runStateful 31 = .outOfFuel spinState := by rfl

/-- A genuine exhaustion at a larger fuel budget excludes both completion and
fault at every smaller budget. This avoids enumerating a cycle's checkpoints. -/
private theorem exhaustion_prefix {spent fuel : Nat} {start suspended : State}
    (exhausted : runStateful spent start = .outOfFuel suspended) (smaller : fuel ≤ spent) :
    ∃ checkpoint, runStateful fuel start = .outOfFuel checkpoint := by
  cases outcome : runStateful fuel start with
  | done value store =>
      obtain ⟨cost, enough, path⟩ := runStateful_sound outcome
      have completed := runStateful_complete_with_fuel path (Nat.le_trans enough smaller)
      rw [completed] at exhausted
      cases exhausted
  | fault error state =>
      obtain ⟨cost, enough, path, terminal⟩ := runStateful_fault_sound outcome
      have fault := runStateful_fault_complete_of_steps path terminal (Nat.le_trans enough smaller)
      rw [fault] at exhausted
      cases exhausted
  | outOfFuel checkpoint => exact ⟨checkpoint, rfl⟩

private theorem spinState_exhausts (fuel : Nat) :
    ∃ checkpoint, runStateful fuel spinState = .outOfFuel checkpoint := by
  induction fuel using Nat.strongRecOn with
  | ind fuel inductionHypothesis =>
      by_cases short : fuel < 53
      · exact exhaustion_prefix spin_cycle (by omega)
      · obtain ⟨checkpoint, exhausted⟩ := inductionHypothesis (fuel - 53) (by omega)
        have resumed := runStateful_resume spin_cycle (fuel - 53)
        have total : 53 + (fuel - 53) = fuel := by omega
        rw [total] at resumed
        exact ⟨checkpoint, resumed.symm.trans exhausted⟩

private theorem spinProgram_exhausts (fuel : Nat) :
    ∃ checkpoint, spinProgram.runStateful fuel = .outOfFuel checkpoint := by
  by_cases short : fuel < 31
  · exact exhaustion_prefix spin_reached (by omega)
  · obtain ⟨checkpoint, exhausted⟩ := spinState_exhausts (fuel - 31)
    have resumed := runStateful_resume spin_reached (fuel - 31)
    have total : 31 + (fuel - 31) = fuel := by omega
    rw [total] at resumed
    exact ⟨checkpoint, resumed.symm.trans exhausted⟩

/-- The all-fuel claim follows from the machine cycle, rather than sampled
timeouts. Each retained state is typed with the cyclic optional-function cell. -/
example (fuel : Nat) : ∃ checkpoint,
    spinProgram.runStateful fuel = .outOfFuel checkpoint ∧
      StateHasType checkpoint spinProgram.resultType := by
  obtain ⟨checkpoint, exhausted⟩ := spinProgram_exhausts fuel
  exact ⟨checkpoint, exhausted, well_typed_runStateful_preserves_checkpoint_type
    (initial_state_has_type (Program.check_full_sound spin_checked).bodyHasType) exhausted⟩

example {value : Value} {store : Store}
    (evaluation : Evaluates [] [] spinProgram.body value store) : False := by
  obtain ⟨required, completes⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluation
  obtain ⟨checkpoint, exhausted⟩ := spinProgram_exhausts required
  change runStateful required (State.initial spinProgram.body) = .outOfFuel checkpoint at exhausted
  rw [completes required (by omega)] at exhausted
  cases exhausted

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expect (testCondition body testPost : Expr) (value : Value)
    (remaining trace : Nat) (message : String) : IO Unit := do
  let fixture := program testCondition body testPost
  assertTrue fixture.check s!"{message}: checker"
  assertTrue (fixture.runStateful 2500 == .done value
    [scalar remaining, scalar trace, .inRight .unit (closure testCondition body testPost)]) message

def run : IO Unit := do
  expect condition whileBody (LocalLoop.fallthrough .word) (.inRight .word (scalar 34)) 0 34
    "while condition/body order or shared count"
  expect condition continuedBody post (.inRight .word (scalar 334)) 0 334
    "for continue must run post before condition"
  let breakBody := .letE (.storeCell (.var 0) (literal 11)) (LocalLoop.breaking .word)
  expect condition breakBody post (.inRight .word (scalar 11)) 3 11
    "break must skip post and continue outside the loop"
  let returnBody := .letE (.storeCell (.var 0) (literal 11)) (LocalLoop.returned (literal 7))
  expect condition returnBody post (.inRight .word (scalar 7)) 3 11
    "return must skip post, next condition and outer tail"
  let failureBody := LanguageResult.failure (LocalLoop.controlType .word)
    (.letE (.storeCell (.var 0) (literal 11)) (.word reason))
  expect condition failureBody post (.inLeft .word (.word reason)) 3 11
    "body failure must retain effects and skip post"
  let failureCondition := LanguageResult.failure .bool
    (.letE (.storeCell (.var 0) (literal 11)) (.word reason))
  expect failureCondition continuedBody post (.inLeft .word (.word reason)) 3 11
    "condition failure must skip body and post"
  let failurePost := LanguageResult.failure (LocalLoop.controlType .word)
    (.letE (.storeCell (.var 0) (literal 111)) (.word reason))
  expect condition continuedBody failurePost (.inLeft .word (.word reason)) 3 111
    "post failure must skip the next condition"
  let breakPost := .letE (.storeCell (.var 0) (literal 111)) (LocalLoop.breaking .word)
  expect condition continuedBody breakPost (.inRight .word (scalar 111)) 3 111
    "total helper handling consumes post break"
  let returnPost := .letE (.storeCell (.var 0) (literal 111)) (LocalLoop.returned (literal 7))
  expect condition continuedBody returnPost (.inRight .word (scalar 7)) 3 111
    "total helper handling propagates post return"

end Tests.CoreLocalLoop
end

section
-- leanmerge: from Solcore.Test.CoreLocalRightWordLessBoundary
/-! The left operand may allocate before a local right reference is evaluated.
An unrestricted right operand can instead expose changed closure captures in
the store; that counterexample deliberately uses raw, untyped cell allocation. -/

set_option autoImplicit false

namespace Tests.CoreLocalRightWordLessBoundary

open Solcore Solcore.Core

private def allocating (allocated left : Word) : Expr := .letE (.newCell .word (.word allocated)) (.word left)
private def comparisonBody : Expr := .letE (.var 1) (.binary .wordGt (.var 0) (.var 1))
private def whole (allocated left : Word) : Expr := (allocating allocated left).wordLt (.var 0)
private def environment (right : Word) (tail : Environment) : Environment := .word right :: tail
private def grown (store : Store) (allocated : Word) : Store := store ++ [.word allocated]
private def result (left right : Word) : Value := .bool (decide (left < right))
private theorem wholeShape (allocated left : Word) :
    whole allocated left = .letE (allocating allocated left) comparisonBody := by
  simp [whole, comparisonBody, Expr.wordLt_expansion, Expr.weakenAt]
private theorem allocatingEvaluation (allocated left : Word) (environment : Environment) (store : Store) :
    Evaluates environment store (allocating allocated left) (.word left) (grown store allocated) :=
  .letE (.newCell .word) .word
private theorem allocatingPath (allocated left : Word) (environment : Environment) (store : Store)
    (continuation : List Frame) :
    Steps 6 ⟨.eval (allocating allocated left) environment, continuation, store⟩
      ⟨.ret (.word left), continuation, grown store allocated⟩ :=
  .cons .enterLet (.cons .enterNewCell (.cons .word (.cons .applyNewCell (.cons .bindLet (.cons .word .refl)))))

theorem left_allocation_is_nonlocal_but_ordinary_word_typing_is_recovered
    (allocated left : Word) (tail : Context) (definitions : DataEnvironment) :
    ¬Expr.LocalFragment (allocating allocated left) ∧
    HasType (.word :: tail) (whole allocated left) .bool definitions ∧
    HasType (.word :: tail) (allocating allocated left) .word definitions ∧
    HasType (.word :: tail) (.var 0) .word definitions := by
  have leftTyped : HasType (.word :: tail) (allocating allocated left) .word definitions :=
    .letE (.newCell .word) .word
  have typed := leftTyped.wordLt (show HasType (.word :: tail) (.var 0) .word definitions from .var rfl)
  have originalOperands := typed.wordLt_inv_local_right .var
  refine ⟨?_, typed, originalOperands.2.1, originalOperands.2.2⟩
  intro fragment
  cases fragment with
  | letE allocation _ => cases allocation

theorem raw_forward_and_inverse_preserve_the_actual_allocated_intermediate_store
    (allocated left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment right tail) store (allocating allocated left) (.word left) (grown store allocated) ∧
    Evaluates (environment right tail) (grown store allocated) (.var 0) (.word right) (grown store allocated) ∧
    Evaluates (environment right tail) store (whole allocated left) (result left right) (grown store allocated) ∧
    (∀ value finalStore, Evaluates (environment right tail) store (whole allocated left) value finalStore →
      value = result left right ∧ finalStore = grown store allocated) := by
  have first := allocatingEvaluation allocated left (environment right tail) store
  have second : Evaluates (environment right tail) (grown store allocated) (.var 0) (.word right)
      (grown store allocated) := .var rfl
  refine ⟨first, second, first.wordLt_local_right second .var, ?_⟩
  intro value finalStore evaluation
  obtain ⟨actualLeft, actualRight, middle, leftEvaluation, rightEvaluation, valueEq⟩ :=
    evaluation.wordLt_inv_local_right .var
  have firstEq := evaluation_deterministic leftEvaluation first
  have leftEq := Value.word.inj firstEq.1
  have middleEq := firstEq.2
  subst actualLeft middle
  have secondEq := evaluation_deterministic rightEvaluation second
  have rightEq := Value.word.inj secondEq.1
  subst actualRight
  exact ⟨valueEq, secondEq.2⟩

theorem allocating_left_and_original_right_paths_compose_to_exactly_sixteen
    (allocated left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 16 ⟨.eval (whole allocated left) (environment right tail), continuation, store⟩
      ⟨.ret (result left right), continuation, grown store allocated⟩ :=
  Frontend.CostStepComposition.wordLt_of_local_right
    (allocatingPath allocated left (environment right tail) store)
    (fun _ => .cons (.var rfl) .refl) .var continuation

private def beforeAllocation (allocated left right : Word) (tail : Environment) (store : Store) : State :=
  ⟨.ret (.word allocated), [.newCellApply .word, .letBody (.word left) (environment right tail),
    .letBody comparisonBody (environment right tail)], store⟩
private def afterAllocation (allocated left right : Word) (tail : Environment) (store : Store) : State :=
  ⟨.ret (.cellRef .word store.length), [.letBody (.word left) (environment right tail),
    .letBody comparisonBody (environment right tail)], grown store allocated⟩
private def beforeRight (allocated left right : Word) (tail : Environment) (store : Store) : State :=
  ⟨.eval (.var 1) (.word left :: environment right tail),
    [.letBody (.binary .wordGt (.var 0) (.var 1)) (.word left :: environment right tail)], grown store allocated⟩

theorem genuine_checkpoints_show_allocation_finishes_before_the_right_reference_starts
    (allocated left right : Word) (tail : Environment) (store : Store) :
    runStateful 4 (State.initial (whole allocated left) (environment right tail) store) =
      .outOfFuel (beforeAllocation allocated left right tail store) ∧
    runStateful 5 (State.initial (whole allocated left) (environment right tail) store) =
      .outOfFuel (afterAllocation allocated left right tail store) ∧
    runStateful 9 (State.initial (whole allocated left) (environment right tail) store) =
      .outOfFuel (beforeRight allocated left right tail store) ∧
    store ≠ grown store allocated := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [wholeShape]; rfl
  · rw [wholeShape]; rfl
  · rw [wholeShape]; rfl
  · intro same
    have lengths := congrArg List.length same
    simp [grown] at lengths

theorem exact_fuel_and_resumption_keep_the_allocated_store_and_pending_right_environment
    (allocated left right : Word) (tail : Environment) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial (whole allocated left) (environment right tail) store) =
      .done (result left right) (grown store allocated) ↔ 16 ≤ fuel) ∧
    ((∃ state, runStateful fuel (State.initial (whole allocated left) (environment right tail) store) =
      .outOfFuel state) ↔ fuel < 16) ∧
    Steps 7 (beforeRight allocated left right tail store) (State.final (result left right) (grown store allocated)) ∧
    runStateful fuel (beforeRight allocated left right tail store) =
      runStateful (9 + fuel) (State.initial (whole allocated left) (environment right tail) store) ∧
    (runStateful fuel (beforeRight allocated left right tail store) =
      .done (result left right) (grown store allocated) ↔ 7 ≤ fuel) := by
  have path := allocating_left_and_original_right_paths_compose_to_exactly_sixteen allocated left right tail store []
  have checkpoint :=
    (genuine_checkpoints_show_allocation_finishes_before_the_right_reference_starts allocated left right tail store).2.2.1
  exact ⟨path.runStateful_done_iff, path.runStateful_outOfFuel_iff, (path.residual_of_outOfFuel checkpoint).2,
    runStateful_resume checkpoint fuel, path.resumed_done_iff checkpoint⟩

/-- An admitted function cell can retain different captures after insertion.
Scalar result typing alone does not give literal final-store equality. -/
private def capturingRight (right : Word) : Expr :=
  .letE (.newCell (.function .unit .unit) (.lambda .unit .unit (.var 0))) (.word right)
private def originalCapture : Value := .closure .unit .unit (.var 0) []
private def shiftedCapture (left : Word) : Value := .closure .unit .unit (.var 0) [.word left]

theorem a_word_returning_right_operand_can_store_distinct_captures_after_insertion
    (left right : Word) (store : Store) :
    ¬Expr.LocalFragment (capturingRight right) ∧
    HasType [] (capturingRight right) .word ∧
    Evaluates [] store (capturingRight right) (.word right) (store ++ [originalCapture]) ∧
    Evaluates [.word left] store ((capturingRight right).weakenAt 0) (.word right)
      (store ++ [shiftedCapture left]) ∧
    store ++ [originalCapture] ≠ store ++ [shiftedCapture left] := by
  refine ⟨?_, ?_, .letE (.newCell .lambda) .word, ?_, ?_⟩
  · intro fragment
    cases fragment with
    | letE allocation _ => cases allocation
  · exact .letE (.newCell (.lambda .unit .unit (.var rfl))) .word
  · simp only [capturingRight, Expr.weakenAt]
    exact .letE (.newCell .lambda) .word
  · intro same
    have captured := (List.cons.inj (List.append_cancel_left same)).1
    cases captured

theorem dropping_the_right_fragment_premise_would_make_the_exact_store_bridge_false
    (left right : Word) (store : Store) :
    Evaluates [] store (.word left) (.word left) store ∧
    Evaluates [] store (capturingRight right) (.word right) (store ++ [originalCapture]) ∧
    Evaluates [] store ((Expr.word left).wordLt (capturingRight right)) (result left right)
      (store ++ [shiftedCapture left]) ∧
    ¬Evaluates [] store ((Expr.word left).wordLt (capturingRight right)) (result left right)
      (store ++ [originalCapture]) := by
  obtain ⟨_, _, originalRight, shiftedRight, different⟩ :=
    a_word_returning_right_operand_can_store_distinct_captures_after_insertion left right store
  have actual : Evaluates [] store ((Expr.word left).wordLt (capturingRight right)) (result left right)
      (store ++ [shiftedCapture left]) := by
    rw [Expr.wordLt_expansion]
    exact .letE .word (.letE shiftedRight (.binary (.var rfl) (.var rfl) rfl))
  refine ⟨.word, originalRight, actual, ?_⟩
  intro impossible
  exact different (evaluation_deterministic impossible actual).2

end Tests.CoreLocalRightWordLessBoundary
end

section
-- leanmerge: from Solcore.Test.CoreLocalRightWordLessProperties
/-! Independent original operand derivations exercise the local-right bridge.
The generated lets retain operand order, nested binders, exact costs and outer
continuations; raw execution uses actual words and stores without typing them. -/

set_option autoImplicit false

namespace Tests.CoreLocalRightWordLess

open Solcore Solcore.Core

private def nested : Expr := .letE (.var 1) (.letE (.var 0) (.var 0))
private def simple : Expr := (Expr.var 0).wordLt (.var 1)
private def comparison : Expr := (Expr.var 0).wordLt nested
private def environment (left right : Word) (tail : Environment) : Environment :=
  .word left :: .word right :: tail
private theorem nestedLocal : nested.LocalFragment := .letE .var (.letE .var .var)
private theorem nestedTyped (tail : Context) (definitions : DataEnvironment) :
    HasType (.word :: .word :: tail) nested .word definitions :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))
private theorem leftEvaluates (left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment left right tail) store (.var 0) (.word left) store := .var rfl
private theorem rightEvaluates (left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment left right tail) store (.var 1) (.word right) store := .var rfl
private theorem nestedEvaluates (left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment left right tail) store nested (.word right) store :=
  .letE (.var rfl) (.letE (.var rfl) (.var rfl))
private theorem leftPath (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 1 ⟨.eval (.var 0) (environment left right tail), continuation, store⟩
      ⟨.ret (.word left), continuation, store⟩ := .cons (.var rfl) .refl
private theorem rightPath (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 1 ⟨.eval (.var 1) (environment left right tail), continuation, store⟩
      ⟨.ret (.word right), continuation, store⟩ := .cons (.var rfl) .refl
private theorem nestedPath (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 7 ⟨.eval nested (environment left right tail), continuation, store⟩
      ⟨.ret (.word right), continuation, store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet
    (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))

theorem expansion_shifts_original_right_reference_but_preserves_nested_binders
    (tail : Context) (definitions : DataEnvironment) :
    comparison = .letE (.var 0) (.letE (.letE (.var 2) (.letE (.var 0) (.var 0)))
      (.binary .wordGt (.var 0) (.var 1))) ∧ comparison.LocalFragment ∧
    HasType (.word :: .word :: tail) comparison .bool definitions :=
  ⟨by simp [comparison, nested, Expr.wordLt_expansion, Expr.weakenAt],
    Expr.LocalFragment.var.wordLt nestedLocal,
    (HasType.var rfl).wordLt (nestedTyped tail definitions)⟩

theorem arbitrary_definition_typing_reflects_both_original_operands_and_bool_result
    {context : Context} {type : Ty} {definitions : DataEnvironment}
    (typing : HasType context comparison type definitions) :
    type = .bool ∧ HasType context (.var 0) .word definitions ∧
      HasType context nested .word definitions := typing.wordLt_inv_local_right nestedLocal

theorem nonword_operands_and_word_result_are_rejected
    (context : Context) (definitions : DataEnvironment) (word : Word) :
    (¬ HasType context ((Expr.bool true).wordLt (.word word)) .bool definitions) ∧
    (¬ HasType context ((Expr.word word).wordLt (.bool false)) .bool definitions) ∧
    (¬ HasType context comparison .word definitions) := by
  refine ⟨?_, ?_, ?_⟩
  · intro typing
    have invalid := (typing.wordLt_inv_local_right .word).2.1
    cases invalid
  · intro typing
    have invalid := (typing.wordLt_inv_local_right .bool).2.2
    cases invalid
  · intro typing
    have invalid := (typing.wordLt_inv_local_right nestedLocal).1
    cases invalid

theorem original_variable_evaluation_equivalence_fixes_actual_words_and_store
    (left right : Word) (tail : Environment) (store finalStore : Store) (value : Value) :
    Evaluates (environment left right tail) store simple value finalStore ↔
      value = .bool (decide (left < right)) ∧ finalStore = store := by
  rw [show simple = (Expr.var 0).wordLt (.var 1) from rfl,
    wordLt_evaluates_iff_local_right (Expr.LocalFragment.var (index := 1))]
  constructor
  · rintro ⟨actualLeft, actualRight, middleStore, first, second, result⟩
    obtain ⟨leftSame, storeSame⟩ := evaluation_deterministic first (leftEvaluates left right tail store)
    cases leftSame
    subst middleStore
    obtain ⟨rightSame, finalSame⟩ := evaluation_deterministic second (rightEvaluates left right tail store)
    cases rightSame
    exact ⟨result, finalSame⟩
  · rintro ⟨rfl, sameStore⟩
    subst finalStore
    exact ⟨left, right, store, leftEvaluates left right tail store, rightEvaluates left right tail store, rfl⟩

theorem nested_right_forward_and_inversion_recover_original_store_and_words
    (left right : Word) (tail : Environment) (store : Store) :
    Evaluates (environment left right tail) store comparison (.bool (decide (left < right))) store ∧
    ∀ value finalStore, Evaluates (environment left right tail) store comparison value finalStore →
      value = .bool (decide (left < right)) ∧ finalStore = store := by
  refine ⟨(leftEvaluates left right tail store).wordLt_local_right
    (nestedEvaluates left right tail store) nestedLocal, ?_⟩
  intro value finalStore evaluation
  obtain ⟨actualLeft, actualRight, middleStore, first, second, result⟩ :=
    evaluation.wordLt_inv_local_right nestedLocal
  obtain ⟨leftSame, storeSame⟩ := evaluation_deterministic first (leftEvaluates left right tail store)
  cases leftSame
  subst middleStore
  obtain ⟨rightSame, finalSame⟩ := evaluation_deterministic second (nestedEvaluates left right tail store)
  cases rightSame
  exact ⟨result, finalSame⟩

theorem equal_strict_and_reversed_words_have_distinct_unsigned_boolean_results
    (left right : Word) (ordered : left < right) (tail : Environment) (store : Store) :
    Evaluates (environment left left tail) store comparison (.bool false) store ∧
    Evaluates (environment left right tail) store comparison (.bool true) store ∧
    Evaluates (environment right left tail) store comparison (.bool false) store := by
  have reversed : ¬right < left := fun opposite => Nat.lt_irrefl left.val (Nat.lt_trans ordered opposite)
  exact ⟨by simpa using (nested_right_forward_and_inversion_recover_original_store_and_words left left tail store).1,
    by simpa [ordered] using (nested_right_forward_and_inversion_recover_original_store_and_words left right tail store).1,
    by simpa [reversed] using (nested_right_forward_and_inversion_recover_original_store_and_words right left tail store).1⟩

theorem missing_original_right_cannot_be_supplied_by_the_generated_left_binding
    (left : Word) (store finalStore : Store) (value : Value) :
    ¬ Evaluates [.word left] store simple value finalStore := by
  intro evaluation
  obtain ⟨_, _, _, _, second, _⟩ := evaluation.wordLt_inv_local_right (Expr.LocalFragment.var (index := 1))
  cases second with
  | var found => cases found

theorem original_variable_paths_compose_to_eleven_steps
    (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 11 ⟨.eval simple (environment left right tail), continuation, store⟩
      ⟨.ret (.bool (decide (left < right))), continuation, store⟩ :=
  Frontend.CostStepComposition.wordLt_of_local_right
    (leftPath left right tail store) (rightPath left right tail store) .var continuation

theorem original_nested_right_paths_compose_to_seventeen_steps
    (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 17 ⟨.eval comparison (environment left right tail), continuation, store⟩
      ⟨.ret (.bool (decide (left < right))), continuation, store⟩ :=
  Frontend.CostStepComposition.wordLt_of_local_right
    (leftPath left right tail store) (nestedPath left right tail store) nestedLocal continuation

theorem exact_fuel_thresholds_distinguish_variable_and_nested_original_right_costs
    (left right : Word) (tail : Environment) (store : Store) (fuel : Nat) :
    (runStateful fuel (State.initial simple (environment left right tail) store) =
      .done (.bool (decide (left < right))) store ↔ 11 ≤ fuel) ∧
    (runStateful fuel (State.initial comparison (environment left right tail) store) =
      .done (.bool (decide (left < right))) store ↔ 17 ≤ fuel) ∧
    ((∃ checkpoint, runStateful fuel (State.initial comparison (environment left right tail) store) =
      .outOfFuel checkpoint) ↔ fuel < 17) := by
  have simplePath := original_variable_paths_compose_to_eleven_steps left right tail store []
  have complexPath := original_nested_right_paths_compose_to_seventeen_steps left right tail store []
  exact ⟨simplePath.runStateful_done_iff, complexPath.runStateful_done_iff, complexPath.runStateful_outOfFuel_iff⟩

theorem retained_outer_negation_costs_one_more_after_comparison_finishes
    (left right : Word) (tail : Environment) (store : Store) (continuation : List Frame) :
    Steps 17 ⟨.eval comparison (environment left right tail), .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (.bool (decide (left < right))), .unaryApply .boolNot :: continuation, store⟩ ∧
    Steps 18 ⟨.eval comparison (environment left right tail), .unaryApply .boolNot :: continuation, store⟩
      ⟨.ret (.bool (!(decide (left < right)))), continuation, store⟩ := by
  have path := original_nested_right_paths_compose_to_seventeen_steps left right tail store
    (.unaryApply .boolNot :: continuation)
  exact ⟨path, path.trans (.cons (.applyUnary rfl) .refl)⟩

end Tests.CoreLocalRightWordLess
end

section
-- leanmerge: from Solcore.Test.CoreLocalSequence
/-! Local statement helpers retain evaluation order, failure effects, lexical
cell references and actual fuel checkpoints. -/

set_option autoImplicit false

namespace Tests.CoreLocalSequence

open Solcore.Core

private def word (value : Nat) : Word := Word.ofNatModulo value
private def literal (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def reason : Word := word 21

example : Evaluates [] []
    (LocalSequence.letUninitialized .word (OptionalCell.read .word (.var 0) reason))
    (.inLeft .word (.word reason)) [.inLeft .word .unit] :=
  LocalSequence.letUninitialized_evaluates .word
    (OptionalCell.read_failure reason (.var rfl) rfl)

/-- A payload inserted at index one leaves the lexical reference at index zero. -/
example : Evaluates [] []
    (LocalSequence.letInitialized .word .word (LanguageResult.success (literal 7))
      (OptionalCell.read .word (.var 0) reason))
    (.inRight .word (scalar 7)) [.inRight .unit (scalar 7)] := by
  apply LocalSequence.letInitialized_success .word .word (.inRight .word)
  simpa [OptionalCell.read, LanguageResult.success, LanguageResult.failure, Expr.weakenAt, scalar, literal] using
    (OptionalCell.read_success (type := .word) (reference := .var 0) reason
      (environment := [.cellRef (OptionalCell.cellType .word) 0, scalar 7])
      (referenceStore := [.inRight .unit (scalar 7)]) (.var rfl) rfl)

private def assignmentProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := LocalSequence.letUninitialized .word
    (LocalSequence.assign .word (.var 0) (LanguageResult.success (literal 7))
      (LocalSequence.discard .word (OptionalCell.write (.var 0) (literal 9))
        (OptionalCell.read .word (.var 0) reason)))
}

private theorem assignment_checked : assignmentProgram.check = true := by
  simp [assignmentProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    LocalSequence.discard, OptionalCell.allocate, OptionalCell.write, OptionalCell.read,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt,
    literal]
  decide

private theorem assignment_completed : assignmentProgram.runStateful 128 =
    .done (.inRight .word (scalar 9)) [.inRight .unit (scalar 9)] := by
  simp [assignmentProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    LocalSequence.discard, OptionalCell.allocate, OptionalCell.write, OptionalCell.read,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.weakenAt,
    literal]
  rfl

/-- Capture the reference first: its effect changes the counter read by the RHS.
The RHS and continuation still share the same original optional cell. -/
private def capturedReferenceProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := LocalSequence.letUninitialized .word
    (.letE (.newCell .word (literal 3))
      (LocalSequence.assign .word
        (.letE (.storeCell (.var 0) (literal 11)) (.var 2))
        (LanguageResult.success (.loadCell (.var 0)))
        (OptionalCell.read .word (.var 1) reason)))
}

example : capturedReferenceProgram.check = true := by
  simp [capturedReferenceProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    OptionalCell.allocate, OptionalCell.read, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  decide

example : capturedReferenceProgram.runStateful 128 =
    .done (.inRight .word (scalar 11)) [.inRight .unit (scalar 11), scalar 11] := by
  simp [capturedReferenceProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    OptionalCell.allocate, OptionalCell.read, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  rfl

/-- Reference and RHS effects are retained on RHS failure. Neither the target
write nor the continuation's counter mutation takes place. -/
private def rhsFailureProgram : Program := {
  resultType := LanguageResult.resultType .unit
  body := LocalSequence.letUninitialized .word
    (.letE (.newCell .word (literal 3))
      (LocalSequence.assign .unit
        (.letE (.storeCell (.var 0) (literal 11)) (.var 2))
        (LanguageResult.failure .word
          (.letE (.storeCell (.var 0) (literal 17)) (.word reason)))
        (LanguageResult.success (.storeCell (.var 0) (literal 99)))))
}

private theorem rhsFailure_checked : rhsFailureProgram.check = true := by
  simp [rhsFailureProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    OptionalCell.allocate, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Expr.weakenAt, literal]
  decide

private theorem rhsFailure_completed : rhsFailureProgram.runStateful 128 =
    .done (.inLeft .unit (.word reason)) [.inLeft .word .unit, scalar 17] := by
  simp [rhsFailureProgram, LocalSequence.letUninitialized, LocalSequence.assign,
    OptionalCell.allocate, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Expr.weakenAt, literal]
  rfl

/-- Initializer effects finish before the new local cell is allocated. The body
uses its new lexical reference and the existing counter reference. -/
private def initializedEffectsProgram : Program := {
  resultType := LanguageResult.resultType (.product .word .word)
  body := .letE (.newCell .word (literal 3))
    (LocalSequence.letInitialized (.product .word .word) .word
      (LanguageResult.success (.letE (.storeCell (.var 0) (literal 11)) (literal 7)))
      (LocalSequence.pair .word .word
        (OptionalCell.read .word (.var 0) reason)
        (LanguageResult.success (.loadCell (.var 1)))))
}

example : initializedEffectsProgram.check = true := by
  simp [initializedEffectsProgram, LocalSequence.letInitialized, LocalSequence.pair,
    OptionalCell.allocateInitialized, OptionalCell.read, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  decide

example : initializedEffectsProgram.runStateful 128 =
    .done (.inRight .word (.pair (scalar 7) (scalar 11)))
      [scalar 11, .inRight .unit (scalar 7)] := by
  simp [initializedEffectsProgram, LocalSequence.letInitialized, LocalSequence.pair,
    OptionalCell.allocateInitialized, OptionalCell.read, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

private def initializerFailureProgram : Program := {
  resultType := LanguageResult.resultType .word
  body := LocalSequence.letInitialized .word .word
    (LanguageResult.failure .word (.letE (.newCell .word (literal 23)) (.word reason)))
    (LanguageResult.success (literal 99))
}

example : initializerFailureProgram.check = true := by
  simp [initializerFailureProgram, LocalSequence.letInitialized,
    OptionalCell.allocateInitialized, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  decide

/-- A failed initializer keeps its preceding allocation and skips allocation
of the optional binding itself. -/
example : initializerFailureProgram.runStateful 64 =
    .done (.inLeft .word (.word reason)) [scalar 23] := by
  simp [initializerFailureProgram, LocalSequence.letInitialized,
    OptionalCell.allocateInitialized, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  rfl

private def discardFailureProgram : Program := {
  resultType := LanguageResult.resultType (.cell .word)
  body := LocalSequence.discard (.cell .word) (LanguageResult.failure .unit (.word reason))
    (LanguageResult.success (.newCell .word (literal 7)))
}

example : discardFailureProgram.check = true := by
  simp [discardFailureProgram, LocalSequence.discard, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  decide

example : discardFailureProgram.runStateful 64 =
    .done (.inLeft (.cell .word) (.word reason)) [] := by
  simp [discardFailureProgram, LocalSequence.discard, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.weakenAt, literal]
  rfl

private def pairProgram : Program := {
  resultType := LanguageResult.resultType (.product .word .word)
  body := .letE (.newCell .word (literal 0))
    (LocalSequence.pair .word .word
      (LanguageResult.success
        (.letE (.storeCell (.var 0) (literal 11)) (.loadCell (.var 1))))
      (LanguageResult.success
        (.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (literal 1)))
          (.loadCell (.var 1)))))
}

example : pairProgram.check = true := by
  simp [pairProgram, LocalSequence.pair, LanguageResult.bind, LanguageResult.success,
    Expr.weakenAt, literal]
  decide

/-- The right element observes the left element's mutation of the same counter. -/
example : pairProgram.runStateful 128 =
    .done (.inRight .word (.pair (scalar 11) (scalar 12))) [scalar 12] := by
  simp [pairProgram, LocalSequence.pair, LanguageResult.bind, LanguageResult.success,
    Expr.weakenAt, literal]
  rfl

private def pairFailureProgram : Program := {
  resultType := LanguageResult.resultType (.product .word .word)
  body := .letE (.newCell .word (literal 0))
    (LocalSequence.pair .word .word
      (LanguageResult.success (.letE (.storeCell (.var 0) (literal 11)) (literal 7)))
      (LanguageResult.failure .word (.letE (.storeCell (.var 0) (literal 12)) (.word reason))))
}

example : pairFailureProgram.check = true := by
  simp [pairFailureProgram, LocalSequence.pair, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  decide

example : pairFailureProgram.runStateful 128 =
    .done (.inLeft (.product .word .word) (.word reason)) [scalar 12] := by
  simp [pairFailureProgram, LocalSequence.pair, LanguageResult.bind, LanguageResult.success,
    LanguageResult.failure, Expr.weakenAt, literal]
  rfl

example (fuel : Nat) :
    (assignmentProgram.runStateful fuel).HasType (LanguageResult.resultType .word) :=
  Program.checked_runStateful_has_type assignment_checked fuel

/-- RHS failure is a typed completion; its genuine intermediate checkpoints
retain both typing and the same run on resume. -/
example (fuel additional : Nat) (checkpoint : State)
    (exhausted : rhsFailureProgram.runStateful fuel = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType (LanguageResult.resultType .unit) ∧
    runStateful additional checkpoint = rhsFailureProgram.runStateful (fuel + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound rhsFailure_checked).bodyHasType)
    exhausted additional

example : ∃ required world,
    RuntimeStoreHasTypes world [.inLeft .word .unit, scalar 17] ∧
    RuntimeValueHasType world (.inLeft .unit (.word reason)) (LanguageResult.resultType .unit) ∧
    ∀ fuel, required ≤ fuel → rhsFailureProgram.runStateful fuel =
      .done (.inLeft .unit (.word reason)) [.inLeft .word .unit, scalar 17] := by
  have evaluation := runStateful_evaluation_sound rhsFailure_completed
  obtain ⟨world, _, stored, typed⟩ := evaluation_preserves_type evaluation
    (Program.check_full_sound rhsFailure_checked).bodyHasType .nil (.nil [])
  obtain ⟨required, completes⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨required, world, stored, typed, completes⟩

end Tests.CoreLocalSequence
end

section
-- leanmerge: from Solcore.Test.CoreRenaming
/-! Focused static regressions for Core renaming and context insertion. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def assertTrue_variant (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def one : Word :=
  Word.ofNatModulo 1

private def dataType : DataTypeId :=
  ⟨0⟩

private def freeVariableLet : Expr :=
  .letE (.word one) (.binary .wordAdd (.var 0) (.var 1))

private theorem freeVariableLetTyping :
    HasType [.word] freeVariableLet .word := by
  exact .letE .word
    (.binary
      (.var (by simp [BinaryOp.leftType]))
      (.var (by simp [BinaryOp.rightType, BinaryOp.leftType])))

private theorem branchesTyping :
    BranchesHaveType [.word] .word [.bool, .unit] [.var 1, .var 1] := by
  exact .cons (.var (by simp)) (.cons (.var (by simp)) .nil)

example :
    HasType (Context.insertAt [.word] 0 .bool)
      (freeVariableLet.rename (Renaming.insertion 0)) .word :=
  freeVariableLetTyping.rename
    (Renaming.insertion_respects_insertAt [.word] 0 .bool)

example :
    BranchesHaveType (Context.insertAt [.word] 0 .unit) .word [.bool, .unit]
      (Expr.renameList [.var 1, .var 1] (Renaming.insertion 0).lift) :=
  branchesTyping.rename
    (Renaming.insertion_respects_insertAt [.word] 0 .unit)

example :
    infer? (Context.insertAt [.word] 0 .bool)
      (freeVariableLet.rename (Renaming.insertion 0)) = some .word :=
  infer_rename (infer_complete freeVariableLetTyping)
    (Renaming.insertion_respects_insertAt [.word] 0 .bool)

private def testBinderLifting : IO Unit := do
  let lambda : Expr :=
    .lambda .word (.product .word .word) (.pair (.var 0) (.var 1))
  let expectedLambda : Expr :=
    .lambda .word (.product .word .word) (.pair (.var 0) (.var 2))
  assertTrue_variant (lambda.weakenAt 0 == expectedLambda)
    "lambda renaming must preserve its binder and shift the free variable"

  let letExpression : Expr :=
    .letE (.var 0) (.pair (.var 0) (.var 1))
  let expectedLet : Expr :=
    .letE (.var 1) (.pair (.var 0) (.var 2))
  assertTrue_variant (letExpression.weakenAt 0 == expectedLet)
    "let renaming must lift only beneath its body binder"

  let caseExpression : Expr :=
    .caseE (.var 0)
      (.pair (.var 0) (.var 1))
      (.pair (.var 1) (.var 0))
  let expectedCase : Expr :=
    .caseE (.var 1)
      (.pair (.var 0) (.var 2))
      (.pair (.var 2) (.var 0))
  assertTrue_variant (caseExpression.weakenAt 0 == expectedCase)
    "case renaming must lift independently beneath both branch binders"

  let matchExpression : Expr :=
    .matchData dataType .word (.var 0) [
      .pair (.var 0) (.var 1),
      .pair (.var 1) (.var 0)
    ]
  let expectedMatch : Expr :=
    .matchData dataType .word (.var 1) [
      .pair (.var 0) (.var 2),
      .pair (.var 2) (.var 0)
    ]
  assertTrue_variant (matchExpression.weakenAt 0 == expectedMatch)
    "matchData renaming must lift beneath every payload branch binder"

private def testIdentityAndComposition : IO Unit := do
  let expression : Expr :=
    .lambda .word .word
      (.letE (.var 1)
        (.matchData dataType .word (.var 2) [.var 0, .var 3]))
  let inner : Renaming := fun index => index + 2
  let outer : Renaming := fun index => index * 2
  assertTrue_variant (expression.rename Renaming.id == expression)
    "identity renaming must preserve a nested expression"
  assertTrue_variant
    ((expression.rename inner).rename outer ==
      expression.rename (outer.comp inner))
    "composition must apply the inner renaming before the outer renaming"

private def testInsertionBoundaries : IO Unit := do
  let context : Context := [.bool, .word]
  let insertedWithin := Context.insertAt context 1 .unit
  assertTrue_variant (insertedWithin == [.bool, .unit, .word])
    "context insertion must place a type at an in-range cutoff"
  assertTrue_variant
    ((Expr.var 0).rename (Renaming.insertion 1) == .var 0 &&
      (Expr.var 1).rename (Renaming.insertion 1) == .var 2)
    "insertion must preserve lower variables and shift variables at the cutoff"
  assertTrue_variant
    (infer? insertedWithin (.var 0) == some .bool &&
      infer? insertedWithin (.var 1) == some .unit &&
      infer? insertedWithin (.var 2) == some .word)
    "context insertion and variable renaming must agree on lookup types"

  let insertedBeyond := Context.insertAt context 5 .unit
  let scopedExpression : Expr := .pair (.var 0) (.var 1)
  assertTrue_variant (insertedBeyond == [.bool, .word, .unit])
    "an insertion beyond the context must saturate at its end"
  assertTrue_variant
    (scopedExpression.rename (Renaming.insertion 5) == scopedExpression)
    "an insertion beyond a context must preserve its well-scoped variables"
  assertTrue_variant
    ((Expr.var 7).rename (Renaming.insertion 5) == .var 8)
    "out-of-range syntax still follows the renaming even when it is untyped"

private def testFreeVariableNoncapture : IO Unit := do
  let expected : Expr :=
    .letE (.word one) (.binary .wordAdd (.var 0) (.var 2))
  let renamed := freeVariableLet.rename (Renaming.insertion 0)
  assertTrue_variant (renamed == expected)
    "head insertion must not capture a free variable beneath a let binder"
  assertTrue_variant
    (infer? (Context.insertAt [.word] 0 .bool) renamed == some .word)
    "the noncapturing renamed expression must retain its inferred type"

/-- Cover static binder lifting, renaming laws, insertion, noncapture, and the
typing-preservation theorem surface. -/
def testCoreRenaming : IO Unit := do
  testBinderLifting
  testIdentityAndComposition
  testInsertionBoundaries
  testFreeVariableNoncapture

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreRenamingRuntime
/-! Dynamic regressions for evaluation under Core environment renaming. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core

private def two : Word := Word.ofNatModulo 2

private theorem renameHeadBoolEmpty
    {environment : Environment} {expr : Expr} {value : Bool}
    (inserted : Value)
    (evaluation : Evaluates environment [] expr (.bool value) []) :
    Evaluates (inserted :: environment) [] (expr.weakenAt 0) (.bool value) [] := by
  obtain ⟨targetValue, targetStore, targetEvaluation, values, stores⟩ :=
    evaluation.rename
      (EnvironmentsRelated.headInsertion inserted environment) .nil
  have valueEquality := ValuesRelated.bool_iff.mp values
  subst targetValue
  cases stores
  simpa using targetEvaluation

private def identityApplication : Expr :=
  .apply (.lambda .word .word (.var 0)) (.var 0)

private theorem lambdaSimulation :
    ∃ targetValue targetStore,
      Evaluates [.bool true, .word one] []
        ((Expr.lambda .word .word (.var 1)).weakenAt 0)
        targetValue targetStore ∧
      ValuesRelated
        (.closure .word .word (.var 1) [.word one]) targetValue ∧
      StoresRelated [] targetStore := by
  have sourceEvaluation :
      Evaluates [.word one] [] (.lambda .word .word (.var 1))
        (.closure .word .word (.var 1) [.word one]) [] :=
    .lambda
  simpa using sourceEvaluation.rename
    (EnvironmentsRelated.headInsertion (.bool true) [.word one]) .nil

private theorem identityApplicationEvaluation :
    Evaluates [.word one] [] identityApplication (.word one) [] := by
  have functionEvaluation :
      Evaluates [.word one] [] (.lambda .word .word (.var 0))
        (.closure .word .word (.var 0) [.word one]) [] :=
    .lambda
  have argumentEvaluation :
      Evaluates [.word one] [] (.var 0) (.word one) [] :=
    .var (by simp)
  have bodyEvaluation :
      Evaluates [.word one, .word one] [] (.var 0) (.word one) [] :=
    .var (by simp)
  exact .apply functionEvaluation argumentEvaluation bodyEvaluation

private theorem identityApplicationTyping :
    HasType [.word] identityApplication .word :=
  infer_sound (by native_decide)

example :
    Evaluates [.bool true, .word one] []
      (identityApplication.weakenAt 0) (.word one) [] :=
  identityApplicationEvaluation.weakenAt_zero_word identityApplicationTyping
    (.cons .word .nil) RuntimeStoreHasTypes.nil StoreHasTypes.nil (.bool true)

private def cellRoundTrip : Expr :=
  .letE
    (.newCell .word (.word Word.zero))
    (.letE
      (.storeCell (.var 0) (.word one))
      (.loadCell (.var 1)))

private theorem cellRoundTripEvaluation :
    Evaluates [] [] cellRoundTrip (.word one) [.word one] := by
  have newEvaluation :
      Evaluates [] [] (.newCell .word (.word Word.zero))
        (.cellRef .word 0) [.word Word.zero] :=
    .newCell .word
  have storeEvaluation :
      Evaluates [.cellRef .word 0] [.word Word.zero]
        (.storeCell (.var 0) (.word one)) .unit [.word one] :=
    Evaluates.storeCell
      (elementType := .word) (location := 0)
      (oldValue := .word Word.zero) (newValue := .word one)
      (.var (by simp)) (by simp [Store.read?]) .word
      (by simp [Store.write?])
  have loadEvaluation :
      Evaluates [.unit, .cellRef .word 0] [.word one]
        (.loadCell (.var 1)) (.word one) [.word one] :=
    Evaluates.loadCell (elementType := .word) (location := 0)
      (.var (by simp)) (by simp [Store.read?])
  exact .letE newEvaluation (.letE storeEvaluation loadEvaluation)

private theorem cellRoundTripTyping :
    HasType [] cellRoundTrip .word :=
  infer_sound (by native_decide)

example :
    Evaluates [.bool false] [] (cellRoundTrip.weakenAt 0)
      (.word one) [.word one] :=
  cellRoundTripEvaluation.weakenAt_zero_word cellRoundTripTyping
    .nil RuntimeStoreHasTypes.nil (StoreHasTypes.nil.allocate .word .word) (.bool false)

private def constructor : ConstructorId := ⟨dataType, 0⟩

private def namedMatch : Expr :=
  .matchData dataType .bool
    (.construct constructor (.bool true))
    [.var 0]

private theorem namedMatchEvaluation :
    Evaluates [] [] namedMatch (.bool true) [] := by
  have scrutineeEvaluation :
      Evaluates [] [] (.construct constructor (.bool true))
        (.constructed constructor (.bool true)) [] :=
    .construct .bool
  have branchEvaluation :
      Evaluates [.bool true] [] (.var 0) (.bool true) [] :=
    .var (by simp)
  exact .matchData scrutineeEvaluation rfl rfl branchEvaluation

example :
    Evaluates [.word two] [] (namedMatch.weakenAt 0) (.bool true) [] :=
  renameHeadBoolEmpty (.word two) namedMatchEvaluation

private theorem freeWordEvaluation :
    Evaluates [.word two] [] (.var 0) (.word two) [] :=
  .var (by simp)

private theorem freeWordTyping :
    HasType [.word] (.var 0) .word :=
  .var (by simp)

example :
    Evaluates [.bool true, .word two] [] ((Expr.var 0).weakenAt 0)
      (.word two) [] :=
  freeWordEvaluation.weakenAt_zero_word freeWordTyping
    (.cons .word .nil) RuntimeStoreHasTypes.nil StoreHasTypes.nil (.bool true)

example :
    HasType [.bool, .word]
      (Expr.wordLt (.word one) ((Expr.var 0).weakenAt 0)) .bool := by
  exact infer_sound (by native_decide)

example :
    HasType [.bool, .word]
      (Expr.wordGe (.word one) ((Expr.var 0).weakenAt 0)) .bool := by
  exact infer_sound (by native_decide)

private def testClosureRelationNotEquality : IO Unit := do
  let source : Value := .closure .word .word (.var 1) [.word one]
  let target : Value :=
    .closure .word .word ((Expr.var 1).rename (Renaming.insertion 0).lift)
      [.bool true, .word one]
  have related : ValuesRelated source target :=
    .closure (Renaming.insertion 0)
      (EnvironmentsRelated.headInsertion (.bool true) [.word one])
  assertTrue_variant (source != target)
    "renamed closures must not require raw structural equality"
  have _ := related
  pure ()

/-- Cover closure relation, application, cells, named matching, and the future
swapped-comparison weakening premise without adding runtime semantics. -/
def testCoreRenamingRuntime : IO Unit := do
  testClosureRelationNotEquality

end Tests
end

section
-- leanmerge: from Solcore.Test.CoreRuntimeStoreSafety
/-! Higher-order store invariants do not traverse cyclic captured references. -/

set_option autoImplicit false

namespace Tests.CoreRuntimeStoreSafety

open Solcore.Core

private def functionType : Ty := .function .unit .unit

private def selfClosure : Value :=
  .closure .unit .unit (.var 0) [.cellRef functionType 0]

private theorem selfClosure_typed :
    RuntimeValueHasType [functionType] selfClosure functionType :=
  .closure (.cons (.cellRef rfl) .nil) (.var rfl)

/-- The closure captures its own location. Typing remains a finite proof. -/
private theorem cyclicStore_typed :
    RuntimeStoreHasTypes [functionType] [selfClosure] where
  length_eq := rfl
  lookup := by
    intro location type found
    cases location with
    | zero =>
        have equal : functionType = type := Option.some.inj found
        subst type
        exact ⟨selfClosure, rfl, selfClosure_typed⟩
    | succ location => simp at found

private def callState : State :=
  .initial (.apply (.var 0) .unit) [selfClosure] [selfClosure]

/-- The pure machine now uses the general world-indexed store invariant. -/
private theorem callState_typed : StateHasType callState .unit :=
  .eval cyclicStore_typed (.cons selfClosure_typed .nil)
    (.apply (.var rfl) .unit) .nil

example (fuel : Nat) (fault : MachineFault) (state : State) :
    runStateful fuel callState ≠ .fault fault state :=
  well_typed_runStateful_never_faults callState_typed

example : runStateful 6 callState = .done .unit [selfClosure] := by
  rfl

private def allocationState : State :=
  .initial (.newCell .bool (.bool true)) [] [selfClosure]

private theorem allocationState_typed : StateHasType allocationState (.cell .bool) :=
  .eval cyclicStore_typed .nil (.newCell .bool) .nil

example : runStateful 3 allocationState =
    .done (.cellRef .bool 1) [selfClosure, .bool true] := by
  rfl

example (fuel : Nat) (checkpoint : State)
    (exhausted : runStateful fuel allocationState = .outOfFuel checkpoint) :
    ∃ future, WorldExtends [functionType] future ∧
      RuntimeStoreHasTypes future checkpoint.store :=
  well_typed_runStateful_preserves_checkpoint_world
    allocationState_typed cyclicStore_typed exhausted

example :
    ∃ value, Store.read? [selfClosure] 0 = some value ∧
      RuntimeValueHasType [functionType] value functionType :=
  cyclicStore_typed.read rfl

/-- Allocation weakens every captured reference to the extended world. -/
example : RuntimeStoreHasTypes [functionType, .bool] [selfClosure, .bool true] :=
  cyclicStore_typed.allocate (.bool : RuntimeValueHasType _ (.bool true) .bool)

/-- Writing a closure with a captured location preserves the store invariant. -/
example : RuntimeStoreHasTypes [functionType] [selfClosure] :=
  cyclicStore_typed.write (location := 0) rfl selfClosure_typed rfl

/-- An annotation without a matching world entry is insufficient. -/
example : ¬ RuntimeValueHasType [functionType]
    (.cellRef functionType 1) (.cell functionType) := by
  intro typing
  cases typing with
  | cellRef found => simp at found

example : ¬ RuntimeStoreHasTypes [functionType] [] := by
  intro typing
  have equal := typing.length_eq
  cases equal

/-- Higher-order constructor payloads retain their nominal environment. -/
private def dataDefinitions : DataEnvironment :=
  [{ constructorPayloadTypes := [functionType] }]

private def constructedClosure : Value :=
  .constructed ⟨⟨0⟩, 0⟩ (.closure .unit .unit (.var 0) [])

example : RuntimeStoreHasTypes [.namedData ⟨0⟩] [constructedClosure]
    dataDefinitions := by
  have valueTyping : RuntimeValueHasType [] constructedClosure
      (.namedData ⟨0⟩) dataDefinitions :=
    .constructed rfl (.closure .nil (.var rfl))
  exact (RuntimeStoreHasTypes.nil dataDefinitions).allocate valueTyping

end Tests.CoreRuntimeStoreSafety
end
