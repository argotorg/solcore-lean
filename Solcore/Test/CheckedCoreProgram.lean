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
    checkedCellProgram.runStateful_has_sufficient_fuel
  exact ⟨required, value, store, completes required (Nat.le_refl required)⟩

private theorem compileTimeNoFaultRegression
    (fuel : Nat)
    (error : MachineFault)
    (faultState : State) :
    checkedCellProgram.runStateful fuel ≠ .fault error faultState :=
  checkedCellProgram.runStateful_ne_fault fuel error faultState

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
