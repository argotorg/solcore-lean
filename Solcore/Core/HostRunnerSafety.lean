import Solcore.Core.HostRunnerProperties
import Solcore.Core.HostTransitionSafety
import Solcore.Core.HostProgress

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
        StoreHasTypes world store ∧
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
        StoreHasTypes world store ∧
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
      StoreHasTypes world store ∧
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
      StoreHasTypes world store ∧
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
