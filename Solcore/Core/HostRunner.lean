import Solcore.Core.HostMachine

/-! Fuelled execution that preserves suspension state and remaining fuel. -/

set_option autoImplicit false

namespace Solcore.Core

inductive HostRunResult where
  | done (value : Value) (store : Store)
  | outOfFuel (state : State)
  | fault (error : MachineFault) (state : State)
  | suspended (suspension : HostSuspension) (remainingFuel : Nat)
  deriving Repr, BEq, DecidableEq

/--
Run until completion, fault, fuel exhaustion, or one host request. Both an
ordinary next step and a request boundary consume one unit of fuel.
-/
def hostRun : Nat → State → HostRunResult
  | fuel, state =>
      match hostAdvance state with
      | .done value => .done value state.store
      | .fault error => .fault error state
      | .next next =>
          match fuel with
          | 0 => .outOfFuel state
          | remaining + 1 => hostRun remaining next
      | .suspended suspension =>
          match fuel with
          | 0 => .outOfFuel state
          | remaining + 1 => .suspended suspension remaining

namespace HostRunResult

/-- Project the remaining budget only from a suspended result. -/
def remainingFuel? : HostRunResult → Option Nat
  | .suspended _ remaining => some remaining
  | _ => none

theorem remainingFuel_lt
    {fuel : Nat}
    {state : State}
    {suspension : HostSuspension}
    {remainingFuel : Nat}
    (result : hostRun fuel state = .suspended suspension remainingFuel) :
    remainingFuel < fuel := by
  induction fuel generalizing state with
  | zero =>
      cases advanced : hostAdvance state <;>
        rw [hostRun, advanced] at result <;>
        cases result
  | succ fuel ih =>
      cases advanced : hostAdvance state with
      | done value =>
          rw [hostRun, advanced] at result
          cases result
      | fault error =>
          rw [hostRun, advanced] at result
          cases result
      | next next =>
          rw [hostRun, advanced] at result
          exact Nat.lt_succ_of_lt (ih result)
      | suspended emitted =>
          rw [hostRun, advanced] at result
          have sameFuel : fuel = remainingFuel :=
            (HostRunResult.suspended.inj result).2
          omega

end HostRunResult

@[simp] theorem hostRun_suspension_zero
    (suspension : HostSuspension)
    (state : State)
    (ready : hostAdvance state = .suspended suspension) :
    hostRun 0 state = .outOfFuel state := by
  simp [hostRun, ready]

@[simp] theorem hostRun_suspension_succ
    (suspension : HostSuspension)
    (state : State)
    (fuel : Nat)
    (ready : hostAdvance state = .suspended suspension) :
    hostRun (fuel + 1) state = .suspended suspension fuel := by
  simp [hostRun, ready]

/-- Start a host-aware program with exactly the fixed capability environment. -/
def Program.runHostStateful
    (program : Program)
    (fuel : Nat) : HostRunResult :=
  hostRun fuel (State.initial program.body hostEnvironment)

end Solcore.Core
