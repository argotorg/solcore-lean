import Solcore.Core.ExactFuelProperties
import Solcore.Core.Correspondence

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
