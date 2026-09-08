import Solcore.Core.MachineProperties

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
