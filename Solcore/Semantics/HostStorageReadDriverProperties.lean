import Solcore.Core.HostRunnerSafety
import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.HostStorageReadDriver

/-! Context preservation and type safety for handled storage-read execution. -/

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

namespace HostStorageReadDriver

@[simp] theorem run_of_done
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    run context fuel state = ⟨context, .done value store⟩ := by
  rw [run, execution]

@[simp] theorem run_of_outOfFuel
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run context fuel state = ⟨context, .outOfFuel exhausted⟩ := by
  rw [run, execution]

@[simp] theorem run_of_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run context fuel state = ⟨context, .fault error faultState⟩ := by
  rw [run, execution]

/-- A request resumes with exactly Core's returned remaining fuel. -/
theorem run_of_suspended
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    run context fuel state =
      run (handleHostSuspension context suspension).1 remainingFuel
        (handleHostSuspension context suspension).2 := by
  rw [run, execution]

@[simp] theorem handleHostSuspension_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleHostSuspension context suspension).1 = context := by
  exact handleStorageReadSuspension_context context suspension

theorem handleHostSuspension_state_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension)
    (typing :
      Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handleHostSuspension context suspension).2
      resultType definitions :=
  handleStorageReadSuspension_state_hasType context suspension typing

/-- A read-only handled run returns the exact context with which it started. -/
@[simp] theorem run_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State) :
    (run context fuel state).context = context := by
  induction fuel using Nat.strongRecOn generalizing context state with
  | ind fuel ih =>
      cases execution : Core.hostRun fuel state with
      | done value store => rw [run, execution]
      | outOfFuel exhausted => rw [run, execution]
      | fault error faultState => rw [run, execution]
      | suspended suspension remainingFuel =>
          rw [run, execution]
          change
            (run (handleHostSuspension context suspension).1 remainingFuel
              (handleHostSuspension context suspension).2).context = context
          calc
            _ = (handleHostSuspension context suspension).1 :=
              ih remainingFuel
                (Core.HostRunResult.remainingFuel_lt execution)
                (handleHostSuspension context suspension).1
                (handleHostSuspension context suspension).2
            _ = context := handleHostSuspension_context context suspension

/-- Handling typed storage requests preserves the terminal result type. -/
theorem run_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping :
      Core.HostStateHasType state resultType definitions) :
    (run context fuel state).outcome.HasType resultType definitions := by
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
          apply handleHostSuspension_state_hasType
          exact Core.hostRun_suspended_hasType stateTyping execution

theorem run_ne_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping :
      Core.HostStateHasType state resultType definitions) :
    (run context fuel state).outcome ≠ .fault error faultState := by
  intro fault
  have typing := run_hasType context fuel state stateTyping
  rw [fault] at typing
  exact typing

end HostStorageReadDriver

namespace CheckedHostCoreProgram

@[simp] theorem runWithStorageReads_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageReadDriver.Context RollbackState TraceState)
    (fuel : Nat) :
    (code.runWithStorageReads context fuel).context = context := by
  exact HostStorageReadDriver.run_context context fuel _

theorem runWithStorageReads_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageReadDriver.Context RollbackState TraceState)
    (fuel : Nat) :
    (code.runWithStorageReads context fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions := by
  exact HostStorageReadDriver.run_hasType context fuel _ code.initialState_hasType

theorem runWithStorageReads_ne_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageReadDriver.Context RollbackState TraceState)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithStorageReads context fuel).outcome ≠
      .fault error faultState := by
  exact HostStorageReadDriver.run_ne_fault context fuel _ faultState error
    code.initialState_hasType

theorem runWithStorageReads_done_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageReadDriver.Context RollbackState TraceState)
    {fuel : Nat}
    {value : Core.Value}
    {store : Core.Store}
    (result :
      (code.runWithStorageReads context fuel).outcome = .done value store) :
    ∃ world,
      Core.StoreHasTypes world store ∧
        Core.HostRuntimeValueHasType world value code.program.resultType
          code.program.dataDefinitions := by
  have typing := code.runWithStorageReads_hasType context fuel
  rw [result] at typing
  exact typing

theorem runWithStorageReads_outOfFuel_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageReadDriver.Context RollbackState TraceState)
    {fuel : Nat}
    {state : Core.State}
    (result :
      (code.runWithStorageReads context fuel).outcome = .outOfFuel state) :
    Core.HostStateHasType state code.program.resultType
      code.program.dataDefinitions := by
  have typing := code.runWithStorageReads_hasType context fuel
  rw [result] at typing
  exact typing

end CheckedHostCoreProgram

end Solcore.Semantics
