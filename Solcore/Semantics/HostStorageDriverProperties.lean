import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteCodeProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties
import Solcore.Semantics.HostStorageDriver
import Solcore.Semantics.HostStorageHandlerProperties

/-! Equations and type safety for combined handled storage execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

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
  simpa only [run] using
    HostDriver.run_of_done
      (@handler RollbackState TraceState)
      context fuel state value store execution

@[simp] theorem run_of_outOfFuel
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run context fuel state = ⟨context, .outOfFuel exhausted⟩ := by
  simpa only [run] using
    HostDriver.run_of_outOfFuel
      (@handler RollbackState TraceState)
      context fuel state exhausted execution

@[simp] theorem run_of_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run context fuel state = ⟨context, .fault error faultState⟩ := by
  simpa only [run] using
    HostDriver.run_of_fault
      (@handler RollbackState TraceState)
      context fuel state faultState error execution

/-- A storage request resumes with exactly Core's returned remaining fuel. -/
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
      run (handleSuspension context suspension).1 remainingFuel
        (handleSuspension context suspension).2 := by
  simpa only [run, handleSuspension] using
    HostDriver.run_of_suspended
      (@handler RollbackState TraceState)
      context fuel remainingFuel state suspension execution

/--
A storage-selector observation resumes with the exact widened Word and exactly
the remaining fuel returned by Core.
-/
theorem run_of_suspended_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.storageAddress, continuation, store⟩ remainingFuel) :
    run context fuel state =
      run context remainingFuel
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩ := by
  calc
    run context fuel state =
        run
          (handleSuspension context
            ⟨.storageAddress, continuation, store⟩).1
          remainingFuel
          (handleSuspension context
            ⟨.storageAddress, continuation, store⟩).2 :=
      run_of_suspended context fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_storageAddress]

/-- A combined handled run retains the selected storage Address. -/
@[simp] theorem run_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State) :
    (run context fuel state).context.context.storageAddress =
      context.context.storageAddress := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState)
      (fun current => current.context.storageAddress)
      (by
        intro current request
        cases request <;> simp [handler, handleRequest])
      context fuel state

/-- A combined handled run retains the complete checkpoint. -/
@[simp] theorem run_checkpoint
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State) :
    (run context fuel state).context.context.values.checkpoint =
      context.context.values.checkpoint := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState)
      (fun current => current.context.values.checkpoint)
      (by
        intro current request
        cases request <;> simp [handler, handleRequest])
      context fuel state

/-- A combined handled run retains the complete working effect journal. -/
@[simp] theorem run_workingEffects
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State) :
    (run context fuel state).context.context.values.working.2 =
      context.context.values.working.2 := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState)
      (fun current => current.context.values.working.2)
      (by
        intro current request
        cases request <;> simp [handler, handleRequest])
      context fuel state

/-- A combined handled run retains checked code at every working Address. -/
@[simp] theorem run_workingCode?
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State)
    (codeAddress : Address) :
    (run context fuel state).context.context.values.working.1.code?
        codeAddress =
      context.context.values.working.1.code? codeAddress := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState)
      (fun current => current.context.values.working.1.code? codeAddress)
      (by
        intro current request
        cases request <;> simp [handler, handleRequest])
      context fuel state

/-- A combined run preserves every non-selected working Account. -/
@[simp] theorem run_workingAccount?_of_ne_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    (run context fuel state).context.context.values.working.1.account?
        observedAddress =
      context.context.values.working.1.account? observedAddress := by
  have preserved :
      (if observedAddress =
          (run context fuel state).context.context.storageAddress then
        none
      else
        (run context fuel state).context.context.values.working.1.account?
          observedAddress) =
      (if observedAddress = context.context.storageAddress then
        none
      else
        context.context.values.working.1.account? observedAddress) := by
    simpa only [run] using
      HostDriver.run_observe
        (@handler RollbackState TraceState)
        (fun current =>
          if observedAddress = current.context.storageAddress then
            none
          else
            current.context.values.working.1.account? observedAddress)
        (by
          intro current request
          cases request with
          | storageRead slot =>
              simp [handler, handleRequest]
          | storageWrite slot value =>
              by_cases same :
                  observedAddress = current.context.storageAddress
              · simp [handler, handleRequest, same]
              · simp [handler, handleRequest, same]
          | storageAddress =>
              simp [handler, handleRequest])
        context fuel state
  simpa only [run_storageAddress, if_neg different] using preserved

/-- A typed start produces only typed combined-driver outcomes. -/
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
    (run context fuel state).outcome.HasType
      resultType definitions := by
  simpa only [run] using
    HostDriver.run_hasType
      (@handler RollbackState TraceState)
      context fuel state stateTyping

/-- A typed start cannot produce a combined-driver fault. -/
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

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorage_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (fuel : Nat) :
    (code.runWithStorage context fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions := by
  exact HostStorageDriver.run_hasType
    context fuel _ code.initialState_hasType

theorem runWithStorage_ne_fault
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithStorage context fuel).outcome ≠
      .fault error faultState := by
  exact HostStorageDriver.run_ne_fault
    context fuel _ faultState error code.initialState_hasType

theorem runWithStorage_done_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    {fuel : Nat}
    {value : Core.Value}
    {store : Core.Store}
    (result :
      (code.runWithStorage context fuel).outcome = .done value store) :
    ∃ world,
      Core.StoreHasTypes world store ∧
        Core.HostRuntimeValueHasType world value code.program.resultType
          code.program.dataDefinitions := by
  have typing := code.runWithStorage_hasType context fuel
  rw [result] at typing
  exact typing

theorem runWithStorage_outOfFuel_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    {fuel : Nat}
    {state : Core.State}
    (result :
      (code.runWithStorage context fuel).outcome = .outOfFuel state) :
    Core.HostStateHasType state code.program.resultType
      code.program.dataDefinitions := by
  have typing := code.runWithStorage_hasType context fuel
  rw [result] at typing
  exact typing

end CheckedHostCoreProgram

end Solcore.Semantics
