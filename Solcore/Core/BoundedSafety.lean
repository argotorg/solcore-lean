import Solcore.Core.Safety
import Solcore.Core.FuelResumptionProperties

/-! Safety of every finite execution, including genuine fuel checkpoints. -/

set_option autoImplicit false

namespace Solcore.Core

/-- Completion has a typed value and store; exhaustion retains a typed state.
An internal machine fault is not an admissible typed outcome. -/
def StatefulRunResult.HasType
    (result : StatefulRunResult) (type : Ty)
    (definitions : DataEnvironment := []) : Prop :=
  match result with
  | .done value store =>
      ∃ world,
        StoreHasTypes world store ∧ RuntimeValueHasType world value type definitions
  | .outOfFuel checkpoint => StateHasType checkpoint type definitions
  | .fault _ _ => False

/-- The actual exhaustion checkpoint has the same result type as the start. -/
theorem well_typed_runStateful_preserves_checkpoint_type
    {definitions : DataEnvironment} {fuel : Nat}
    {start checkpoint : State} {type : Ty}
    (typing : StateHasType start type definitions)
    (exhausted : runStateful fuel start = .outOfFuel checkpoint) :
    StateHasType checkpoint type definitions :=
  (runStateful_outOfFuel_sound exhausted).1.preserve_state_type typing

/-- Finite safety needs no termination assumption or sufficient-fuel bound. -/
theorem well_typed_runStateful_has_type
    {definitions : DataEnvironment} {state : State} {type : Ty}
    (typing : StateHasType state type definitions) (fuel : Nat) :
    (runStateful fuel state).HasType type definitions := by
  cases result : runStateful fuel state with
  | done value store =>
      exact well_typed_runStateful_preserves_result_type typing result
  | outOfFuel checkpoint =>
      exact well_typed_runStateful_preserves_checkpoint_type typing result
  | fault error faultState =>
      exact False.elim (well_typed_runStateful_never_faults typing result)

/-- Resume the retained typed state, preserving the complete outcome invariant. -/
theorem well_typed_runStateful_resume_has_type
    {definitions : DataEnvironment} {spent : Nat}
    {start checkpoint : State} {type : Ty}
    (typing : StateHasType start type definitions)
    (exhausted : runStateful spent start = .outOfFuel checkpoint)
    (additional : Nat) :
    (runStateful additional checkpoint).HasType type definitions ∧
      runStateful additional checkpoint = runStateful (spent + additional) start :=
  ⟨well_typed_runStateful_has_type
      (well_typed_runStateful_preserves_checkpoint_type typing exhausted) additional,
    runStateful_resume exhausted additional⟩

theorem Program.checked_runStateful_has_type
    {program : Program} (checked : program.check = true) (fuel : Nat) :
    (program.runStateful fuel).HasType program.resultType program.dataDefinitions :=
  well_typed_runStateful_has_type
    (initial_state_has_type (Program.check_full_sound checked).bodyHasType) fuel

end Solcore.Core
