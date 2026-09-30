import Solcore.Core.BoundedSafety

/-! A checked program installs a closure in the cell that it captures and
then calls it forever. General cells require finite safety, not normalization. -/

set_option autoImplicit false

namespace Tests.CoreGeneralCells

open Solcore.Core

private def functionType : Ty := .function .unit .unit

private def recursiveBody : Expr :=
  .apply (.loadCell (.var 1)) .unit

private def recursiveClosure : Value :=
  .closure .unit .unit recursiveBody [.cellRef functionType 0]

private def loopState : State :=
  .initial recursiveBody [.unit, .cellRef functionType 0] [recursiveClosure]

/-- Allocation and mutation construct the cycle from an empty initial store. -/
private def recursiveProgram : Program := {
  resultType := .unit
  body :=
    .letE (.newCell functionType (.lambda .unit .unit .unit))
      (.letE (.storeCell (.var 0) (.lambda .unit .unit recursiveBody))
        recursiveBody)
}

private theorem recursiveProgram_checked : recursiveProgram.check = true := by
  decide

/-- The loop is a genuine machine cycle, including the same captured reference,
store and empty continuation. -/
private theorem loop_cycle : runStateful 7 loopState = .outOfFuel loopState := by
  rfl

private theorem reaches_loop :
    runStateful 12 (.initial recursiveProgram.body) = .outOfFuel loopState := by
  rfl

private theorem loop_exhausts (fuel : Nat) :
    ∃ checkpoint, runStateful fuel loopState = .outOfFuel checkpoint := by
  induction fuel using Nat.strongRecOn with
  | ind fuel inductionHypothesis =>
      by_cases short : fuel < 7
      · have cases : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨
            fuel = 4 ∨ fuel = 5 ∨ fuel = 6 := by omega
        rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨_, rfl⟩
      · obtain ⟨checkpoint, exhausted⟩ :=
          inductionHypothesis (fuel - 7) (by omega)
        refine ⟨checkpoint, ?_⟩
        have resumed := runStateful_resume loop_cycle (fuel - 7)
        have sum : 7 + (fuel - 7) = fuel := by omega
        rw [sum] at resumed
        exact resumed.symm.trans exhausted

/-- This checked program has no finite successful evaluation. The proof uses
the actual machine cycle and semantics correspondence, not a timeout sample. -/
private theorem recursiveProgram_no_evaluation
    {value : Value} {store : Store}
    (evaluation : Evaluates [] [] recursiveProgram.body value store) : False := by
  obtain ⟨required, completes⟩ :=
    evaluation_runStateful_complete_with_sufficient_fuel evaluation
  obtain ⟨checkpoint, exhausted⟩ := loop_exhausts required
  have resumed := runStateful_resume reaches_loop required
  rw [exhausted, completes (12 + required) (by omega)] at resumed
  cases resumed

/-- Every fuel budget suspends, with no internal fault and no forged completion. -/
private theorem recursiveProgram_exhausts (fuel : Nat) :
    ∃ checkpoint, recursiveProgram.runStateful fuel = .outOfFuel checkpoint := by
  cases outcome : recursiveProgram.runStateful fuel with
  | done value store =>
      exact False.elim (recursiveProgram_no_evaluation
        (runStateful_evaluation_sound outcome))
  | outOfFuel checkpoint => exact ⟨checkpoint, rfl⟩
  | fault error state =>
      exact False.elim (Program.checked_runStateful_never_faults
        recursiveProgram_checked outcome)

example (fuel : Nat) :
    ∃ checkpoint,
      recursiveProgram.runStateful fuel = .outOfFuel checkpoint ∧
      StateHasType checkpoint .unit := by
  obtain ⟨checkpoint, exhausted⟩ := recursiveProgram_exhausts fuel
  exact ⟨checkpoint, exhausted,
    well_typed_runStateful_preserves_checkpoint_type
      (initial_state_has_type
        (Program.check_full_sound recursiveProgram_checked).bodyHasType) exhausted⟩

example (fuel additional : Nat) (checkpoint : State)
    (exhausted : recursiveProgram.runStateful fuel = .outOfFuel checkpoint) :
    (runStateful additional checkpoint).HasType .unit ∧
      runStateful additional checkpoint = recursiveProgram.runStateful (fuel + additional) :=
  well_typed_runStateful_resume_has_type
    (initial_state_has_type
      (Program.check_full_sound recursiveProgram_checked).bodyHasType)
    exhausted additional

/-- A captured reference that has no matching world entry is still invalid. -/
example : ¬ RuntimeValueHasType []
    (.cellRef functionType 0) (.cell functionType) := by
  intro typing
  cases typing with
  | cellRef found => cases found

end Tests.CoreGeneralCells
