import Solcore.Core.HostRunnerSafety
import Solcore.Semantics.HostDriver

/-! Observation preservation and type safety for generic handled execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostDriverOutcome

/-- Typed terminal outcomes exclude the raw fault branch. -/
def HasType
    (outcome : HostDriverOutcome)
    (resultType : Core.Ty)
    (definitions : Core.DataEnvironment := []) : Prop :=
  match outcome with
  | .done value store =>
      ∃ world,
        Core.StoreHasTypes world store ∧
          Core.HostRuntimeValueHasType world value resultType definitions
  | .outOfFuel state =>
      Core.HostStateHasType state resultType definitions
  | .fault _ _ => False

@[simp] theorem done_hasType_iff
    {value : Core.Value}
    {store : Core.Store}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment} :
    HasType (.done value store) resultType definitions ↔
      ∃ world,
        Core.StoreHasTypes world store ∧
          Core.HostRuntimeValueHasType world value resultType definitions := by
  rfl

@[simp] theorem outOfFuel_hasType_iff
    {state : Core.State}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment} :
    HasType (.outOfFuel state) resultType definitions ↔
      Core.HostStateHasType state resultType definitions := by
  rfl

@[simp] theorem fault_not_hasType
    {error : Core.MachineFault}
    {state : Core.State}
    {resultType : Core.Ty}
    {definitions : Core.DataEnvironment} :
    ¬ HasType (.fault error state) resultType definitions := by
  simp [HasType]

end HostDriverOutcome

namespace HostHandler

/-- Every dependent handler response resumes a typed suspension safely. -/
theorem handleSuspension_state_hasType
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (suspension : Core.HostSuspension)
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (typing :
      Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handler.handleSuspension context suspension).2
      resultType definitions := by
  unfold handleSuspension
  exact typing.resume (handler.handle context suspension.request).2

end HostHandler

namespace HostDriver

@[simp] theorem run_of_done
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    run handler context fuel state =
      ⟨context, .done value store⟩ := by
  rw [run, execution]

@[simp] theorem run_of_outOfFuel
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run handler context fuel state =
      ⟨context, .outOfFuel exhausted⟩ := by
  rw [run, execution]

@[simp] theorem run_of_fault
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run handler context fuel state =
      ⟨context, .fault error faultState⟩ := by
  rw [run, execution]

/-- A request resumes with exactly Core's returned remaining fuel. -/
theorem run_of_suspended
    {Context : Type u}
    (handler : HostHandler Context)
    (context : Context)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    run handler context fuel state =
      run handler
        (handler.handleSuspension context suspension).1
        remainingFuel
        (handler.handleSuspension context suspension).2 := by
  rw [run, execution]

/-- Any observation preserved by one handler call is preserved by a whole run. -/
theorem run_observe
    {Context : Type u}
    {Observation : Type v}
    (handler : HostHandler Context)
    (observe : Context → Observation)
    (handleObserve :
      ∀ context request,
        observe (handler.handle context request).1 = observe context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State) :
    observe (run handler context fuel state).context = observe context := by
  induction fuel using Nat.strongRecOn generalizing context state with
  | ind fuel ih =>
      cases execution : Core.hostRun fuel state with
      | done value store => rw [run, execution]
      | outOfFuel exhausted => rw [run, execution]
      | fault error faultState => rw [run, execution]
      | suspended suspension remainingFuel =>
          rw [run, execution]
          calc
            observe
                (run handler
                  (handler.handleSuspension context suspension).1
                  remainingFuel
                  (handler.handleSuspension context suspension).2).context =
                observe (handler.handleSuspension context suspension).1 :=
              ih remainingFuel
                (Core.HostRunResult.remainingFuel_lt execution)
                (handler.handleSuspension context suspension).1
                (handler.handleSuspension context suspension).2
            _ = observe context := by
              simpa [HostHandler.handleSuspension] using
                handleObserve context suspension.request

/-- A typed start remains typed across every dependent handled response. -/
theorem run_hasType
    {Context : Type u}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping :
      Core.HostStateHasType state resultType definitions) :
    (run handler context fuel state).outcome.HasType
      resultType definitions := by
  induction fuel using Nat.strongRecOn generalizing context state with
  | ind fuel ih =>
      cases execution : Core.hostRun fuel state with
      | done value store =>
          rw [run, execution]
          exact Core.hostRun_done_hasType stateTyping execution
      | outOfFuel exhausted =>
          rw [run, execution]
          exact Core.hostRun_outOfFuel_hasType stateTyping execution
      | fault error faultState =>
          rw [run, execution]
          exact Core.hostRun_never_faults stateTyping execution
      | suspended suspension remainingFuel =>
          rw [run, execution]
          apply ih remainingFuel
            (Core.HostRunResult.remainingFuel_lt execution)
          apply handler.handleSuspension_state_hasType
          exact Core.hostRun_suspended_hasType stateTyping execution

/-- A generic handled run cannot expose a fault from a typed start. -/
theorem run_ne_fault
    {Context : Type u}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (handler : HostHandler Context)
    (context : Context)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping :
      Core.HostStateHasType state resultType definitions) :
    (run handler context fuel state).outcome ≠
      .fault error faultState := by
  intro fault
  have typing := run_hasType handler context fuel state stateTyping
  rw [fault] at typing
  exact typing

end HostDriver

end Solcore.Semantics
