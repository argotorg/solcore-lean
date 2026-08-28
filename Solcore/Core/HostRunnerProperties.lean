import Solcore.Core.HostMachineProperties
import Solcore.Core.HostRunner

/-! Relational soundness of the fuelled host-aware Core runner. -/

set_option autoImplicit false

namespace Solcore.Core

inductive HostSteps : Nat → State → State → Prop where
  | refl {state : State} : HostSteps 0 state state
  | cons
      {steps : Nat} {start next finish : State} :
      HostTransition start next →
      HostSteps steps next finish →
      HostSteps (steps + 1) start finish

@[simp] theorem HostAdvanceResult.ofAdvance_eq_done_iff
    {result : AdvanceResult}
    {value : Value} :
    HostAdvanceResult.ofAdvance result = .done value ↔ result = .done value := by
  cases result <;> simp

theorem hostAdvance_done_iff
    {state : State}
    {value : Value} :
    hostAdvance state = .done value ↔
      ∃ store, state = State.final value store := by
  constructor
  · intro advanced
    rcases state with ⟨control, continuation, store⟩
    cases control with
    | eval expr environment =>
        exact advance_done_iff.mp (by simpa [hostAdvance] using advanced)
    | ret returned =>
        cases continuation with
        | nil =>
            exact advance_done_iff.mp (by simpa [hostAdvance] using advanced)
        | cons frame continuation =>
            cases frame <;>
              try
                exact advance_done_iff.mp (by simpa [hostAdvance] using advanced)
            case applyArgument argument environment =>
              cases returned with
              | hostFunction function => simp [hostAdvance] at advanced
              | unit | bool | word | pair | closure | inLeft | inRight | cellRef |
                  constructed =>
                  exact advance_done_iff.mp
                    (by simpa [hostAdvance] using advanced)
            case hostApply function =>
              cases function
              cases returned <;> simp [hostAdvance] at advanced
  · rintro ⟨store, rfl⟩
    simp [hostAdvance, State.final, advance]

theorem hostRun_done_sound
    {fuel : Nat}
    {state : State}
    {value : Value}
    {store : Store}
    (result : hostRun fuel state = .done value store) :
    ∃ steps,
      steps ≤ fuel ∧ HostSteps steps state (State.final value store) := by
  induction fuel generalizing state with
  | zero =>
      cases advanced : hostAdvance state with
      | done returned =>
          rw [hostRun, advanced] at result
          cases result
          obtain ⟨finalStore, rfl⟩ := hostAdvance_done_iff.mp advanced
          exact ⟨0, Nat.zero_le _, .refl⟩
      | next next => rw [hostRun, advanced] at result; cases result
      | fault error => rw [hostRun, advanced] at result; cases result
      | suspended suspension => rw [hostRun, advanced] at result; cases result
  | succ fuel ih =>
      cases advanced : hostAdvance state with
      | done returned =>
          rw [hostRun, advanced] at result
          cases result
          obtain ⟨finalStore, rfl⟩ := hostAdvance_done_iff.mp advanced
          exact ⟨0, Nat.zero_le _, .refl⟩
      | next next =>
          rw [hostRun, advanced] at result
          obtain ⟨steps, bound, path⟩ := ih result
          exact ⟨steps + 1, Nat.succ_le_succ bound,
            .cons (hostAdvance_next_iff.mp advanced) path⟩
      | fault error => rw [hostRun, advanced] at result; cases result
      | suspended suspension => rw [hostRun, advanced] at result; cases result

theorem hostRun_fault_sound
    {fuel : Nat}
    {state faultState : State}
    {error : MachineFault}
    (result : hostRun fuel state = .fault error faultState) :
    ∃ steps,
      steps ≤ fuel ∧
      HostSteps steps state faultState ∧
      hostAdvance faultState = .fault error := by
  induction fuel generalizing state with
  | zero =>
      cases advanced : hostAdvance state with
      | fault actualError =>
          rw [hostRun, advanced] at result
          cases result
          exact ⟨0, Nat.zero_le _, .refl, advanced⟩
      | next next => rw [hostRun, advanced] at result; cases result
      | done value => rw [hostRun, advanced] at result; cases result
      | suspended suspension => rw [hostRun, advanced] at result; cases result
  | succ fuel ih =>
      cases advanced : hostAdvance state with
      | fault actualError =>
          rw [hostRun, advanced] at result
          cases result
          exact ⟨0, Nat.zero_le _, .refl, advanced⟩
      | next next =>
          rw [hostRun, advanced] at result
          obtain ⟨steps, bound, path, terminal⟩ := ih result
          exact ⟨steps + 1, Nat.succ_le_succ bound,
            .cons (hostAdvance_next_iff.mp advanced) path, terminal⟩
      | done value => rw [hostRun, advanced] at result; cases result
      | suspended suspension => rw [hostRun, advanced] at result; cases result

theorem hostRun_suspended_sound
    {fuel remainingFuel : Nat}
    {state : State}
    {suspension : HostSuspension}
    (result : hostRun fuel state = .suspended suspension remainingFuel) :
    ∃ steps requestState,
      HostSteps steps state requestState ∧
      HostRequestEmission requestState suspension ∧
      steps + remainingFuel + 1 = fuel := by
  induction fuel generalizing state with
  | zero =>
      cases advanced : hostAdvance state <;>
        rw [hostRun, advanced] at result <;>
        cases result
  | succ fuel ih =>
      cases advanced : hostAdvance state with
      | done value => rw [hostRun, advanced] at result; cases result
      | fault error => rw [hostRun, advanced] at result; cases result
      | next next =>
          rw [hostRun, advanced] at result
          obtain ⟨steps, requestState, path, emission, accounting⟩ := ih result
          exact ⟨steps + 1, requestState,
            .cons (hostAdvance_next_iff.mp advanced) path, emission, by omega⟩
      | suspended emitted =>
          rw [hostRun, advanced] at result
          have suspensionEq : emitted = suspension :=
            (HostRunResult.suspended.inj result).1
          have fuelEq : fuel = remainingFuel :=
            (HostRunResult.suspended.inj result).2
          subst emitted
          exact ⟨0, state, .refl, hostAdvance_suspended_iff.mp advanced, by omega⟩

theorem hostRun_outOfFuel_sound
    {fuel : Nat}
    {state exhausted : State}
    (result : hostRun fuel state = .outOfFuel exhausted) :
    HostSteps fuel state exhausted ∧
      ((∃ next, HostTransition exhausted next) ∨
        ∃ suspension, HostRequestEmission exhausted suspension) := by
  induction fuel generalizing state with
  | zero =>
      cases advanced : hostAdvance state with
      | done value => rw [hostRun, advanced] at result; cases result
      | fault error => rw [hostRun, advanced] at result; cases result
      | next next =>
          rw [hostRun, advanced] at result
          cases result
          exact ⟨.refl, .inl ⟨next, hostAdvance_next_iff.mp advanced⟩⟩
      | suspended suspension =>
          rw [hostRun, advanced] at result
          cases result
          exact ⟨.refl,
            .inr ⟨suspension, hostAdvance_suspended_iff.mp advanced⟩⟩
  | succ fuel ih =>
      cases advanced : hostAdvance state with
      | done value => rw [hostRun, advanced] at result; cases result
      | fault error => rw [hostRun, advanced] at result; cases result
      | suspended suspension => rw [hostRun, advanced] at result; cases result
      | next next =>
          rw [hostRun, advanced] at result
          obtain ⟨path, ready⟩ := ih result
          exact ⟨.cons (hostAdvance_next_iff.mp advanced) path, ready⟩

end Solcore.Core
