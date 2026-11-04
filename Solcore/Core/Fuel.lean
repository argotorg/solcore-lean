import Solcore.Core.Internal.MachineLaws
import Solcore.Core.Correspondence

/-!
# Fuel accounting

`Steps.final_unique`: the length of a path to a final state is unique, so the path has an exact
cost. `Steps.runStateful_done_iff` and `Steps.runStateful_outOfFuel_iff` say what a run does with
any fuel. `runStateful_resume`: continuing from an exhausted state is one larger run. `Steps.residual_of_outOfFuel`,
`Steps.resumed_done_iff` and `Steps.resumed_outOfFuel_iff` give the exact cost that remains.
-/

section
-- leanmerge: from Solcore.Core.ExactFuelProperties
/-! Exact fuel thresholds for a known terminating Core path. Length uniqueness
is restricted to final states, never arbitrary intermediate endpoints. -/

set_option autoImplicit false

namespace Solcore.Core

private theorem final_has_no_transition {value : Value} {store : Store} {next : State}
    (transition : Transition (State.final value store) next) : False := by
  have advanced := advance_next_iff.mpr transition
  simp [advance, State.final] at advanced

theorem Steps.final_unique {leftSteps rightSteps : Nat} {start : State}
    {left right : Value} {leftStore rightStore : Store}
    (leftPath : Steps leftSteps start (State.final left leftStore))
    (rightPath : Steps rightSteps start (State.final right rightStore)) :
    leftSteps = rightSteps ∧ left = right ∧ leftStore = rightStore := by
  induction leftSteps generalizing rightSteps start with
  | zero =>
      cases leftPath
      cases rightPath with
      | refl => exact ⟨rfl, rfl, rfl⟩
      | cons transition _ => exact False.elim (final_has_no_transition transition)
  | succ steps ih =>
      cases leftPath with
      | cons leftStep leftTail =>
          cases rightPath with
          | refl => exact False.elim (final_has_no_transition leftStep)
          | cons rightStep rightTail =>
              cases transition_deterministic leftStep rightStep
              obtain ⟨sameSteps, sameValue, sameStore⟩ := ih leftTail rightTail
              exact ⟨congrArg (fun count => count + 1) sameSteps, sameValue, sameStore⟩

theorem Steps.runStateful_done_iff {steps fuel : Nat} {start : State}
    {value : Value} {finalStore : Store}
    (path : Steps steps start (State.final value finalStore)) :
    runStateful fuel start = .done value finalStore ↔ steps ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨actualSteps, enough, actualPath⟩ := runStateful_sound completed
    exact (path.final_unique actualPath).1.symm ▸ enough
  · exact runStateful_complete_with_fuel path

private theorem exhausted_of_short_path {steps fuel : Nat} {start finish : State}
    (path : Steps steps start finish) (short : fuel < steps) :
    ∃ suspended, runStateful fuel start = .outOfFuel suspended := by
  induction path generalizing fuel with
  | refl => omega
  | cons transition tail ih =>
      have advanced := advance_next_iff.mpr transition
      cases fuel with
      | zero => exact ⟨_, by rw [runStateful, advanced]⟩
      | succ remaining =>
          obtain ⟨suspended, result⟩ := ih (fuel := remaining) (by omega)
          exact ⟨suspended, by rw [runStateful, advanced]; exact result⟩

theorem Steps.runStateful_outOfFuel_iff {steps fuel : Nat} {start : State}
    {value : Value} {finalStore : Store}
    (path : Steps steps start (State.final value finalStore)) :
    (∃ suspended, runStateful fuel start = .outOfFuel suspended) ↔ fuel < steps := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    by_cases short : fuel < steps
    · exact short
    · have completed := runStateful_complete_with_fuel path (by omega : steps ≤ fuel)
      rw [completed] at exhausted
      cases exhausted
  · exact exhausted_of_short_path path

end Solcore.Core
end

section
-- leanmerge: from Solcore.Core.FuelResumptionProperties
/-! Exact fuel accounting after a genuine Core exhaustion checkpoint. Resumption
retains the actual state and introduces no transition. Arbitrary programs may
be resumed; exact residual costs additionally require a known terminating path. -/

set_option autoImplicit false

namespace Solcore.Core

/-- Continuing the actual exhausted state is identical to one larger run,
including every final, exhausted, or fault result. No typing or termination
premise is needed, but an arbitrary replacement checkpoint is not permitted. -/
theorem runStateful_resume {spent : Nat} {start checkpoint : State}
    (exhausted : runStateful spent start = .outOfFuel checkpoint) (additional : Nat) :
    runStateful additional checkpoint = runStateful (spent + additional) start := by
  have prefixPath := (runStateful_outOfFuel_sound exhausted).1
  clear exhausted
  induction prefixPath with
  | refl => simp only [Nat.zero_add]
  | @cons steps start next finish transition tail ih =>
      have advanced := advance_next_iff.mpr transition
      calc
        runStateful additional finish = runStateful (steps + additional) next := ih
        _ = runStateful (steps + 1 + additional) start := by
          symm
          rw [Nat.add_right_comm steps 1 additional, runStateful, advanced]

/-- A genuine checkpoint on a known final path has consumed strictly less
than its exact cost, and retains precisely the unconsumed suffix. Length
uniqueness is used only after joining paths to the same final state. -/
theorem Steps.residual_of_outOfFuel {cost spent : Nat} {start checkpoint : State}
    {value : Value} {finalStore : Store}
    (path : Steps cost start (State.final value finalStore))
    (exhausted : runStateful spent start = .outOfFuel checkpoint) :
    spent < cost ∧ Steps (cost - spent) checkpoint (State.final value finalStore) := by
  have short : spent < cost := path.runStateful_outOfFuel_iff.mp ⟨checkpoint, exhausted⟩
  have resumed : runStateful (cost - spent) checkpoint = .done value finalStore :=
    (runStateful_resume exhausted (cost - spent)).trans
      (path.runStateful_done_iff.mpr (by omega))
  obtain ⟨remaining, _, residual⟩ := runStateful_sound resumed
  have prefixPath := (runStateful_outOfFuel_sound exhausted).1
  have lengthEq := (path.final_unique (prefixPath.trans residual)).1
  have remainingEq : remaining = cost - spent := by omega
  exact ⟨short, remainingEq ▸ residual⟩

theorem Steps.resumed_done_iff {cost spent additional : Nat} {start checkpoint : State}
    {value : Value} {finalStore : Store}
    (path : Steps cost start (State.final value finalStore))
    (exhausted : runStateful spent start = .outOfFuel checkpoint) :
    runStateful additional checkpoint = .done value finalStore ↔ cost - spent ≤ additional :=
  (path.residual_of_outOfFuel exhausted).2.runStateful_done_iff

/-- Further exhaustion quantifies the next actual suspended state; it does
not reset the source environment or discard the checkpoint's continuation. -/
theorem Steps.resumed_outOfFuel_iff {cost spent additional : Nat} {start checkpoint : State}
    {value : Value} {finalStore : Store}
    (path : Steps cost start (State.final value finalStore))
    (exhausted : runStateful spent start = .outOfFuel checkpoint) :
    (∃ suspended, runStateful additional checkpoint = .outOfFuel suspended) ↔ additional < cost - spent :=
  (path.residual_of_outOfFuel exhausted).2.runStateful_outOfFuel_iff

end Solcore.Core
end
