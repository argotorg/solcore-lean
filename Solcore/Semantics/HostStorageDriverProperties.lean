import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteCodeProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteProjectionProperties
import Solcore.Semantics.HostDriverProperties
import Solcore.Semantics.HostStorageDriver
import Solcore.Semantics.HostStorageHandlerProperties

/-! Execution and preservation laws for the canonical storage host driver. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

universe u v

@[simp] theorem run_of_done
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    run context inputs fuel state =
      ⟨context, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_of_done
      (@handler RollbackState TraceState inputs)
      context fuel state value store execution

@[simp] theorem run_of_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run context inputs fuel state =
      ⟨context, .outOfFuel exhausted⟩ := by
  simpa only [run] using
    HostDriver.run_of_outOfFuel
      (@handler RollbackState TraceState inputs)
      context fuel state exhausted execution

@[simp] theorem run_of_fault
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run context inputs fuel state =
      ⟨context, .fault error faultState⟩ := by
  simpa only [run] using
    HostDriver.run_of_fault
      (@handler RollbackState TraceState inputs)
      context fuel state faultState error execution

/-- Every suspension resumes under the same immutable input. -/
theorem run_of_suspended
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    run context inputs fuel state =
      run
        (handleSuspension inputs context suspension).1 inputs
        remainingFuel
        (handleSuspension inputs context suspension).2 := by
  simpa only [run, handleSuspension] using
    HostDriver.run_of_suspended
      (@handler RollbackState TraceState inputs)
      context fuel remainingFuel state suspension execution

theorem run_of_suspended_storageAddress
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
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.storageAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.storageAddress, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _
        execution
    _ = _ := by rw [handleSuspension_storageAddress]

theorem run_of_suspended_codeAddress
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
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.codeAddress)), continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.codeAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.codeAddress, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _
        execution
    _ = _ := by rw [handleSuspension_codeAddress]

theorem run_of_suspended_callValue
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.callValue, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word inputs.callValue), continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.callValue, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.callValue, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_callValue]

theorem run_of_suspended_callerAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.callerAddress, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.callerAddress)),
          continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.callerAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.callerAddress, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_callerAddress]

theorem run_of_suspended_currentAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.currentAddress, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.currentAddress)),
          continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.currentAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.currentAddress, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_currentAddress]

theorem run_of_suspended_inputDataByte?
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataByte? offset, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ((Core.HostSuspension.mk (.inputDataByte? offset) continuation store).resume
          (inputs.inputData.byte? offset)) := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.inputDataByte? offset, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.inputDataByte? offset, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_inputDataByte?]

theorem run_of_suspended_inputDataByte?_none
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataByte? offset, continuation, store⟩ remainingFuel)
    (absent : inputs.inputData.byte? offset = none) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.inLeft .word .unit), continuation, store⟩ := by
  rw [run_of_suspended_inputDataByte? context inputs fuel remainingFuel state
    offset continuation store execution, absent]
  rfl

theorem run_of_suspended_inputDataByte?_some
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset byte : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataByte? offset, continuation, store⟩ remainingFuel)
    (present : inputs.inputData.byte? offset = some byte) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.inRight .unit (.word byte)), continuation, store⟩ := by
  rw [run_of_suspended_inputDataByte? context inputs fuel remainingFuel state
    offset continuation store execution, present]
  rfl

theorem run_of_suspended_inputDataSize
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataSize, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word inputs.inputData.sizeWord), continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.inputDataSize, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.inputDataSize, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_inputDataSize]

theorem run_of_suspended_inputDataWordBE?
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataWordBE? offset, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ((Core.HostSuspension.mk (.inputDataWordBE? offset) continuation store).resume
          (inputs.inputData.wordBE? offset)) := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.inputDataWordBE? offset, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.inputDataWordBE? offset, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_inputDataWordBE?]

theorem run_of_suspended_inputDataWordBE?_none
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataWordBE? offset, continuation, store⟩ remainingFuel)
    (absent : inputs.inputData.wordBE? offset = none) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.inLeft .word .unit), continuation, store⟩ := by
  rw [run_of_suspended_inputDataWordBE? context inputs fuel remainingFuel state
    offset continuation store execution, absent]
  rfl

theorem run_of_suspended_inputDataWordBE?_some
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset word : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataWordBE? offset, continuation, store⟩ remainingFuel)
    (present : inputs.inputData.wordBE? offset = some word) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.inRight .unit (.word word)), continuation, store⟩ := by
  rw [run_of_suspended_inputDataWordBE? context inputs fuel remainingFuel state
    offset continuation store execution, present]
  rfl

@[simp] theorem run_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.storageAddress =
      context.context.storageAddress := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState inputs)
      (fun current => current.context.storageAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest])
      context fuel state

@[simp] theorem run_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.values.checkpoint =
      context.context.values.checkpoint := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState inputs)
      (fun current => current.context.values.checkpoint)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest])
      context fuel state

@[simp] theorem run_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.values.working.2 =
      context.context.values.working.2 := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState inputs)
      (fun current => current.context.values.working.2)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest])
      context fuel state

@[simp] theorem run_workingCode?
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address) :
    (run context inputs fuel state).context.context.values.working.1.code?
        observedAddress =
      context.context.values.working.1.code? observedAddress := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState inputs)
      (fun current =>
        current.context.values.working.1.code? observedAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest])
      context fuel state

@[simp] theorem run_workingAccount?_of_ne_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    (run context inputs fuel state).context.context.values.working.1.account?
        observedAddress =
      context.context.values.working.1.account? observedAddress := by
  have preserved :
      (if observedAddress =
          (run context inputs fuel state).context.context.storageAddress
        then none
        else
          (run context inputs fuel state).context.context.values.working.1.account?
            observedAddress) =
      (if observedAddress = context.context.storageAddress
        then none
        else context.context.values.working.1.account? observedAddress) := by
    simpa only [run] using
      HostDriver.run_observe
        (@handler RollbackState TraceState inputs)
        (fun current =>
          if observedAddress = current.context.storageAddress
            then none
            else current.context.values.working.1.account? observedAddress)
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
              simp [handler, handleRequest]
          | codeAddress =>
              simp [handler, handleRequest]
          | callValue =>
              simp [handler, handleRequest]
          | callerAddress =>
              simp [handler, handleRequest]
          | currentAddress =>
              simp [handler, handleRequest]
          | inputDataByte? offset =>
              simp [handler, handleRequest]
          | inputDataSize =>
              simp [handler, handleRequest]
          | inputDataWordBE? offset =>
              simp [handler, handleRequest]
          | callContractWord target input =>
              simp [handler, handleRequest])
        context fuel state
  simpa only [run_storageAddress, if_neg different] using preserved

end Solcore.Semantics.HostStorageDriver
