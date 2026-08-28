import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.HostDriverProperties
import Solcore.Semantics.HostStorageReadDriver

/-! Context preservation and type safety for handled storage-read execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

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
  rw [run, HostDriver.run, execution]

@[simp] theorem run_of_outOfFuel
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run context fuel state = ⟨context, .outOfFuel exhausted⟩ := by
  rw [run, HostDriver.run, execution]

@[simp] theorem run_of_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run context fuel state = ⟨context, .fault error faultState⟩ := by
  rw [run, HostDriver.run, execution]

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
  simpa only [run, handler_handleSuspension] using
    HostDriver.run_of_suspended handler context fuel remainingFuel state
      suspension execution

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
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState)
      (fun current => current)
      (fun current request => by cases request; rfl)
      context fuel state

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
  simpa only [run] using
    HostDriver.run_hasType
      (@handler RollbackState TraceState)
      context fuel state stateTyping

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
  simpa only [run] using
    HostDriver.run_ne_fault
      (@handler RollbackState TraceState)
      context fuel state faultState error stateTyping

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
