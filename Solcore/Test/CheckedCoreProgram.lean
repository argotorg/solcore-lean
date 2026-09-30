import Solcore.ContractRuntime.CheckedCoreProgram

/-! Admission, stateful execution, and safety regressions for checked code. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.ContractRuntime

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def cellProgram : Program := {
  resultType := .cell .bool
  body := .newCell .bool (.bool true)
}

private def rejectedProgram : Program := {
  resultType := .unit
  body := .var 0
}

private theorem cellProgram_checked : cellProgram.check = true := by
  decide

private theorem rejectedProgram_rejected : rejectedProgram.check = false := by
  decide

private def checkedCellProgram : CheckedCoreProgram :=
  ⟨cellProgram, cellProgram_checked⟩

private theorem compileTimeAdmissionRegression :
    CheckedCoreProgram.ofProgram? cellProgram = some checkedCellProgram := by
  exact CheckedCoreProgram.ofProgram?_of_checked
    cellProgram cellProgram_checked

private theorem compileTimeRejectionRegression :
    CheckedCoreProgram.ofProgram? rejectedProgram = none := by
  exact CheckedCoreProgram.ofProgram?_of_rejected
    rejectedProgram rejectedProgram_rejected

private theorem compileTimeCompletionRegression :
    ∃ fuel value store,
      checkedCellProgram.runStateful fuel = .done value store := by
  obtain ⟨required, _, store, value, _, _, completes⟩ :=
    checkedCellProgram.runStateful_has_sufficient_fuel (Evaluates.newCell .bool)
  exact ⟨required, value, store, completes required (Nat.le_refl required)⟩

private theorem compileTimeNoFaultRegression
    (fuel : Nat)
    (error : MachineFault)
    (faultState : State) :
    checkedCellProgram.runStateful fuel ≠ .fault error faultState :=
  checkedCellProgram.runStateful_ne_fault fuel error faultState

private theorem compileTimeBoundedSafetyRegression (fuel : Nat) :
    (checkedCellProgram.runStateful fuel).HasType (.cell .bool) :=
  checkedCellProgram.runStateful_has_type fuel

/-- Exhaustion preserves the pending allocation rather than resetting entry. -/
private theorem compileTimeCheckpointRegression :
    StateHasType ⟨.ret (.bool true), [.newCellApply .bool], []⟩ (.cell .bool) := by
  exact well_typed_runStateful_preserves_checkpoint_type
    (initial_state_has_type (Program.check_full_sound cellProgram_checked).bodyHasType)
    (fuel := 2) rfl

private theorem compileTimeTypedResumeRegression (additional : Nat) :
    (runStateful additional
      ⟨.ret (.bool true), [.newCellApply .bool], []⟩).HasType (.cell .bool) ∧
      runStateful additional ⟨.ret (.bool true), [.newCellApply .bool], []⟩ =
        cellProgram.runStateful (2 + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type (Program.check_full_sound cellProgram_checked).bodyHasType)
    (spent := 2) rfl additional

def testCheckedCoreProgram : IO Unit := do
  match CheckedCoreProgram.ofProgram? cellProgram with
  | none =>
      throw (IO.userError "a checker-accepted program was rejected")
  | some code =>
      assertTrue (code.program == cellProgram)
        "admission must retain the exact checked program"
      assertTrue
        (code.runStateful 3 == .done (.cellRef .bool 0) [.bool true])
        "checked execution must retain a cell result and its final local store"
      match code.runStateful 2 with
      | .outOfFuel _ => pure ()
      | result =>
          throw (IO.userError
            s!"insufficient fuel returned an unexpected result: {reprStr result}")
  match CheckedCoreProgram.ofProgram? rejectedProgram with
  | none => pure ()
  | some _ =>
      throw (IO.userError "an ill-typed program entered checked code")

end Tests
