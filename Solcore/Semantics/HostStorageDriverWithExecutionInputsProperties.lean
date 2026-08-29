import Solcore.Semantics.HostStorageDriverProperties
import Solcore.Semantics.HostStorageDriverWithExecutionInputs
import Solcore.Semantics.HostStorageHandlerWithExecutionInputsProperties

/-! Execution and preservation laws for the explicit-input driver seam. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

universe u v

@[simp] theorem runWithInputs_of_done
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    runWithInputs context inputs fuel state =
      ⟨context, .done value store⟩ := by
  simpa only [runWithInputs] using
    HostDriver.run_of_done
      (@handlerWithInputs RollbackState TraceState inputs)
      context fuel state value store execution

@[simp] theorem runWithInputs_of_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    runWithInputs context inputs fuel state =
      ⟨context, .outOfFuel exhausted⟩ := by
  simpa only [runWithInputs] using
    HostDriver.run_of_outOfFuel
      (@handlerWithInputs RollbackState TraceState inputs)
      context fuel state exhausted execution

@[simp] theorem runWithInputs_of_fault
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    runWithInputs context inputs fuel state =
      ⟨context, .fault error faultState⟩ := by
  simpa only [runWithInputs] using
    HostDriver.run_of_fault
      (@handlerWithInputs RollbackState TraceState inputs)
      context fuel state faultState error execution

/-- Every suspension resumes under the same immutable input. -/
theorem runWithInputs_of_suspended
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    runWithInputs context inputs fuel state =
      runWithInputs
        (handleSuspensionWithInputs inputs context suspension).1 inputs
        remainingFuel
        (handleSuspensionWithInputs inputs context suspension).2 := by
  simpa only [runWithInputs, handleSuspensionWithInputs] using
    HostDriver.run_of_suspended
      (@handlerWithInputs RollbackState TraceState inputs)
      context fuel remainingFuel state suspension execution

theorem runWithInputs_of_suspended_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.storageAddress, continuation, store⟩ remainingFuel) :
    runWithInputs context inputs fuel state =
      runWithInputs context inputs remainingFuel
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩ := by
  calc
    runWithInputs context inputs fuel state =
        runWithInputs
          (handleSuspensionWithInputs inputs context
            ⟨.storageAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspensionWithInputs inputs context
            ⟨.storageAddress, continuation, store⟩).2 :=
      runWithInputs_of_suspended context inputs fuel remainingFuel state _
        execution
    _ = _ := by rw [handleSuspensionWithInputs_storageAddress]

theorem runWithInputs_of_suspended_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.codeAddress, continuation, store⟩ remainingFuel) :
    runWithInputs context inputs fuel state =
      runWithInputs context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.codeAddress)), continuation, store⟩ := by
  calc
    runWithInputs context inputs fuel state =
        runWithInputs
          (handleSuspensionWithInputs inputs context
            ⟨.codeAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspensionWithInputs inputs context
            ⟨.codeAddress, continuation, store⟩).2 :=
      runWithInputs_of_suspended context inputs fuel remainingFuel state _
        execution
    _ = _ := by rw [handleSuspensionWithInputs_codeAddress]

@[simp] theorem runWithInputs_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (runWithInputs context inputs fuel state).context.context.storageAddress =
      context.context.storageAddress := by
  simpa only [runWithInputs] using
    HostDriver.run_observe
      (@handlerWithInputs RollbackState TraceState inputs)
      (fun current => current.context.storageAddress)
      (by
        intro current request
        cases request <;>
          simp [handlerWithInputs, handleRequestWithInputs])
      context fuel state

@[simp] theorem runWithInputs_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (runWithInputs context inputs fuel state).context.context.values.checkpoint =
      context.context.values.checkpoint := by
  simpa only [runWithInputs] using
    HostDriver.run_observe
      (@handlerWithInputs RollbackState TraceState inputs)
      (fun current => current.context.values.checkpoint)
      (by
        intro current request
        cases request <;>
          simp [handlerWithInputs, handleRequestWithInputs])
      context fuel state

@[simp] theorem runWithInputs_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (runWithInputs context inputs fuel state).context.context.values.working.2 =
      context.context.values.working.2 := by
  simpa only [runWithInputs] using
    HostDriver.run_observe
      (@handlerWithInputs RollbackState TraceState inputs)
      (fun current => current.context.values.working.2)
      (by
        intro current request
        cases request <;>
          simp [handlerWithInputs, handleRequestWithInputs])
      context fuel state

@[simp] theorem runWithInputs_workingCode?
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address) :
    (runWithInputs context inputs fuel state).context.context.values.working.1.code?
        observedAddress =
      context.context.values.working.1.code? observedAddress := by
  simpa only [runWithInputs] using
    HostDriver.run_observe
      (@handlerWithInputs RollbackState TraceState inputs)
      (fun current =>
        current.context.values.working.1.code? observedAddress)
      (by
        intro current request
        cases request <;>
          simp [handlerWithInputs, handleRequestWithInputs])
      context fuel state

@[simp] theorem runWithInputs_workingAccount?_of_ne_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    (runWithInputs context inputs fuel state).context.context.values.working.1.account?
        observedAddress =
      context.context.values.working.1.account? observedAddress := by
  have preserved :
      (if observedAddress =
          (runWithInputs context inputs fuel state).context.context.storageAddress
        then none
        else
          (runWithInputs context inputs fuel state).context.context.values.working.1.account?
            observedAddress) =
      (if observedAddress = context.context.storageAddress
        then none
        else context.context.values.working.1.account? observedAddress) := by
    simpa only [runWithInputs] using
      HostDriver.run_observe
        (@handlerWithInputs RollbackState TraceState inputs)
        (fun current =>
          if observedAddress = current.context.storageAddress
            then none
            else current.context.values.working.1.account? observedAddress)
        (by
          intro current request
          cases request with
          | storageRead slot =>
              simp [handlerWithInputs, handleRequestWithInputs]
          | storageWrite slot value =>
              by_cases same :
                  observedAddress = current.context.storageAddress
              · simp [handlerWithInputs, handleRequestWithInputs, same]
              · simp [handlerWithInputs, handleRequestWithInputs, same]
          | storageAddress =>
              simp [handlerWithInputs, handleRequestWithInputs]
          | codeAddress =>
              simp [handlerWithInputs, handleRequestWithInputs])
        context fuel state
  simpa only [runWithInputs_storageAddress, if_neg different] using preserved

end Solcore.Semantics.HostStorageDriver
