import Solcore.Core.HostMachine
import Solcore.Core.HostTransitionSafety
import Solcore.Core.HostProgress

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

/-!
## Consolidated module: `Solcore.Core.HostRunnerProperties`
-/

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

/-- Host-aware Core paths compose in execution order. -/
theorem HostSteps.trans
    {leftSteps rightSteps : Nat}
    {start middle finish : State}
    (left : HostSteps leftSteps start middle)
    (right : HostSteps rightSteps middle finish) :
    HostSteps (leftSteps + rightSteps) start finish := by
  induction left with
  | refl => simpa using right
  | cons transition tail tailIH =>
      have combined := tailIH right
      have prefixed := HostSteps.cons transition combined
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using prefixed

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
              | unit | bool | word | integer | pair | closure | inLeft | inRight | cellRef |
                  constructed =>
                  exact advance_done_iff.mp
                    (by simpa [hostAdvance] using advanced)
            case hostApply function =>
              cases function with
              | storageRead =>
                  cases returned <;> simp [hostAdvance] at advanced
              | storageWrite =>
                  cases returned with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp [hostAdvance] at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | storageAddress =>
                  cases returned <;> simp [hostAdvance] at advanced
              | codeAddress =>
                  cases returned <;> simp [hostAdvance] at advanced
              | callValue =>
                  cases returned <;> simp [hostAdvance] at advanced
              | callerAddress =>
                  cases returned <;> simp [hostAdvance] at advanced
              | inputDataByte? =>
                  cases returned <;> simp [hostAdvance] at advanced
              | inputDataSize =>
                  cases returned <;> simp [hostAdvance] at advanced
              | inputDataWordBE? =>
                  cases returned <;> simp [hostAdvance] at advanced
              | currentAddress =>
                  cases returned <;> simp [hostAdvance] at advanced
              | callContractWord =>
                  cases returned with
                  | pair left right =>
                      cases left <;> cases right <;>
                        simp [hostAdvance] at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | callContractWordWithValue =>
                  cases returned with
                  | pair target rest =>
                      cases target <;>
                        try simp [hostAdvance] at advanced
                      case word =>
                        cases rest with
                        | pair transferredValue input =>
                            cases transferredValue <;> cases input <;>
                              simp at advanced
                        | unit | bool | word | integer | hostFunction | closure | inLeft |
                            inRight | cellRef | constructed =>
                            simp at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | createContractWord =>
                  cases returned with
                  | pair templateId rest =>
                      cases templateId <;>
                        try simp [hostAdvance] at advanced
                      case word =>
                        cases rest with
                        | pair transferredValue input =>
                            cases transferredValue <;> cases input <;>
                              simp at advanced
                        | unit | bool | word | integer | hostFunction | closure | inLeft |
                            inRight | cellRef | constructed =>
                            simp at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
              | emitLogWord =>
                  cases returned with
                  | pair topic payload =>
                      cases topic <;> cases payload <;>
                        simp [hostAdvance] at advanced
                  | unit | bool | word | integer | hostFunction | closure | inLeft |
                      inRight | cellRef | constructed =>
                      simp [hostAdvance] at advanced
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

theorem hostRun_done_complete_of_steps
    {steps fuel : Nat}
    {start finish : State}
    {value : Value}
    (path : HostSteps steps start finish)
    (terminal : hostAdvance finish = .done value)
    (enough : steps ≤ fuel) :
    hostRun fuel start = .done value finish.store := by
  induction path generalizing fuel with
  | refl => simp [hostRun, terminal]
  | @cons steps start next finish transition path ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [hostRun, hostAdvance_next_iff.mpr transition]
          exact ih terminal (by omega)

theorem hostRun_done_complete
    {steps fuel : Nat}
    {start : State}
    {value : Value}
    {store : Store}
    (path : HostSteps steps start (State.final value store))
    (enough : steps ≤ fuel) :
    hostRun fuel start = .done value store := by
  exact hostRun_done_complete_of_steps path
    (hostAdvance_done_iff.mpr ⟨store, rfl⟩) enough

theorem hostRun_fault_complete_of_steps
    {steps fuel : Nat}
    {start faultState : State}
    {error : MachineFault}
    (path : HostSteps steps start faultState)
    (terminal : hostAdvance faultState = .fault error)
    (enough : steps ≤ fuel) :
    hostRun fuel start = .fault error faultState := by
  induction path generalizing fuel with
  | refl => simp [hostRun, terminal]
  | @cons steps start next finish transition path ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [hostRun, hostAdvance_next_iff.mpr transition]
          exact ih terminal (by omega)

theorem hostRun_suspended_complete_of_steps
    {steps fuel remainingFuel : Nat}
    {start requestState : State}
    {suspension : HostSuspension}
    (path : HostSteps steps start requestState)
    (emission : HostRequestEmission requestState suspension)
    (accounting : steps + remainingFuel + 1 = fuel) :
    hostRun fuel start = .suspended suspension remainingFuel := by
  induction path generalizing fuel with
  | refl =>
      subst fuel
      simp [hostAdvance_suspended_iff.mpr emission]
  | @cons steps start next finish transition path ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [hostRun, hostAdvance_next_iff.mpr transition]
          exact ih emission (by omega)

theorem hostRun_outOfFuel_complete
    {fuel : Nat}
    {start exhausted : State}
    (path : HostSteps fuel start exhausted)
    (ready :
      (∃ next, HostTransition exhausted next) ∨
        ∃ suspension, HostRequestEmission exhausted suspension) :
    hostRun fuel start = .outOfFuel exhausted := by
  induction path with
  | refl =>
      rcases ready with ⟨next, transition⟩ | ⟨suspension, emission⟩
      · simp [hostRun, hostAdvance_next_iff.mpr transition]
      · simp [hostAdvance_suspended_iff.mpr emission]
  | @cons steps start next finish transition path ih =>
      rw [hostRun, hostAdvance_next_iff.mpr transition]
      exact ih ready

end Solcore.Core

/-!
## Consolidated module: `Solcore.Core.HostRunnerSafety`
-/

/-! Type safety for the fuelled host-aware Core runner. -/

set_option autoImplicit false

namespace Solcore.Core

namespace HostRunResult

/--
A runner result is typed when completion returns a typed value and store,
exhaustion retains a typed state, and suspension retains a typed request.
There is deliberately no typed fault result.
-/
def HasType
    (result : HostRunResult)
    (resultType : Ty)
    (definitions : DataEnvironment := []) : Prop :=
  match result with
  | .done value store =>
      ∃ world,
        HostStoreHasTypes world store definitions ∧
          HostRuntimeValueHasType world value resultType definitions
  | .outOfFuel state => HostStateHasType state resultType definitions
  | .fault _ _ => False
  | .suspended suspension _ =>
      HostSuspensionHasType suspension resultType definitions

@[simp] theorem done_hasType_iff
    {value : Value} {store : Store} {resultType : Ty}
    {definitions : DataEnvironment} :
    HasType (.done value store) resultType definitions ↔
      ∃ world,
        HostStoreHasTypes world store definitions ∧
          HostRuntimeValueHasType world value resultType definitions := by
  rfl

@[simp] theorem outOfFuel_hasType_iff
    {state : State} {resultType : Ty} {definitions : DataEnvironment} :
    HasType (.outOfFuel state) resultType definitions ↔
      HostStateHasType state resultType definitions := by
  rfl

@[simp] theorem fault_not_hasType
    {error : MachineFault} {state : State} {resultType : Ty}
    {definitions : DataEnvironment} :
    ¬ HasType (.fault error state) resultType definitions := by
  simp [HasType]

@[simp] theorem suspended_hasType_iff
    {suspension : HostSuspension} {remainingFuel : Nat} {resultType : Ty}
    {definitions : DataEnvironment} :
    HasType (.suspended suspension remainingFuel) resultType definitions ↔
      HostSuspensionHasType suspension resultType definitions := by
  rfl

end HostRunResult

theorem HostSteps.preserve
    {definitions : DataEnvironment}
    {steps : Nat} {start finish : State} {resultType : Ty}
    (path : HostSteps steps start finish)
    (typing : HostStateHasType start resultType definitions) :
    HostStateHasType finish resultType definitions := by
  induction path with
  | refl => exact typing
  | cons transition _ tail =>
      exact tail (hostTransition_preserves_state_type typing transition)

theorem HostStateHasType.final_components
    {definitions : DataEnvironment}
    {value : Value} {store : Store} {resultType : Ty}
    (typing : HostStateHasType (State.final value store) resultType definitions) :
    ∃ world,
      HostStoreHasTypes world store definitions ∧
        HostRuntimeValueHasType world value resultType definitions := by
  cases typing with
  | ret storeTyping valueTyping continuationTyping =>
      cases continuationTyping with
      | nil => exact ⟨_, storeTyping, valueTyping⟩

theorem hostRun_hasType
    {definitions : DataEnvironment}
    {state : State} {resultType : Ty}
    (fuel : Nat)
    (stateTyping : HostStateHasType state resultType definitions) :
    HostRunResult.HasType (hostRun fuel state) resultType definitions := by
  cases result : hostRun fuel state with
  | done value store =>
      obtain ⟨_, _, path⟩ := hostRun_done_sound result
      exact (path.preserve stateTyping).final_components
  | outOfFuel exhausted =>
      obtain ⟨path, _⟩ := hostRun_outOfFuel_sound result
      exact path.preserve stateTyping
  | fault error faultState =>
      obtain ⟨_, _, path, terminal⟩ := hostRun_fault_sound result
      exact (well_typed_host_state_never_faults
        (path.preserve stateTyping)) terminal
  | suspended suspension remainingFuel =>
      obtain ⟨_, requestState, path, emission, _⟩ :=
        hostRun_suspended_sound result
      exact hostRequestEmission_hasType
        (path.preserve stateTyping) emission

theorem hostRun_done_hasType
    {definitions : DataEnvironment}
    {fuel : Nat} {state : State} {resultType : Ty}
    {value : Value} {store : Store}
    (stateTyping : HostStateHasType state resultType definitions)
    (result : hostRun fuel state = .done value store) :
    ∃ world,
      HostStoreHasTypes world store definitions ∧
        HostRuntimeValueHasType world value resultType definitions := by
  have typing := hostRun_hasType fuel stateTyping
  rw [result] at typing
  exact typing

theorem hostRun_outOfFuel_hasType
    {definitions : DataEnvironment}
    {fuel : Nat} {state exhausted : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (result : hostRun fuel state = .outOfFuel exhausted) :
    HostStateHasType exhausted resultType definitions := by
  have typing := hostRun_hasType fuel stateTyping
  rw [result] at typing
  exact typing

theorem hostRun_suspended_hasType
    {definitions : DataEnvironment}
    {fuel remainingFuel : Nat} {state : State} {resultType : Ty}
    {suspension : HostSuspension}
    (stateTyping : HostStateHasType state resultType definitions)
    (result : hostRun fuel state = .suspended suspension remainingFuel) :
    HostSuspensionHasType suspension resultType definitions := by
  have typing := hostRun_hasType fuel stateTyping
  rw [result] at typing
  exact typing

theorem hostRun_never_faults
    {definitions : DataEnvironment}
    {fuel : Nat} {state faultState : State} {resultType : Ty}
    {error : MachineFault}
    (stateTyping : HostStateHasType state resultType definitions) :
    hostRun fuel state ≠ .fault error faultState := by
  intro result
  have typing := hostRun_hasType fuel stateTyping
  rw [result] at typing
  exact typing

end Solcore.Core
