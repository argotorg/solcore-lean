import Solcore.ContractRuntime.CheckedHostCoreProgram
import Solcore.ContractRuntime.HostDriver
import Solcore.ContractRuntime.HostStorageHandler
import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Canonical driver for storage-backed host execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostStorageDriver

/-- Run the current handler using one immutable execution input. -/
def run
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    HostDriverResult (Context RollbackState TraceState) :=
  HostDriver.run (handler inputs) context fuel state

end HostStorageDriver

namespace CheckedHostCoreProgram

/-- Start checked code with one immutable execution input. -/
def runWithStorage
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostDriverResult
      (HostStorageDriver.Context RollbackState TraceState) :=
  HostStorageDriver.run context inputs fuel
    (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverProperties`
-/

/-! Execution and preservation laws for the canonical storage host driver. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

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
      if (@handler RollbackState TraceState inputs).supports
          suspension.request then
        run
          (handleSuspension inputs context suspension).1 inputs
          remainingFuel
          (handleSuspension inputs context suspension).2
      else
        ⟨context, .unsupported suspension remainingFuel⟩ := by
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

theorem run_of_suspended_emitLogWord
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended
          ⟨.emitLogWord topic payload, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      ⟨context,
        .unsupported
          ⟨.emitLogWord topic payload, continuation, store⟩
          remainingFuel⟩ := by
  simpa [run, handler] using
    HostDriver.run_of_unsupported (handler inputs) context fuel remainingFuel
      state ⟨.emitLogWord topic payload, continuation, store⟩ execution rfl

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
    exact
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
              simp [handler, handleRequest] <;> rfl
          | storageWrite slot value =>
              by_cases same :
                  observedAddress = current.context.storageAddress
              · simp [handler, handleRequest, same]
              · simp [handler, handleRequest, same]
          | storageAddress =>
              simp [handler, handleRequest] <;> rfl
          | codeAddress =>
              simp [handler, handleRequest] <;> rfl
          | callValue =>
              simp [handler, handleRequest] <;> rfl
          | callerAddress =>
              simp [handler, handleRequest] <;> rfl
          | currentAddress =>
              simp [handler, handleRequest] <;> rfl
          | inputDataByte? offset =>
              simp [handler, handleRequest] <;> rfl
          | inputDataSize =>
              simp [handler, handleRequest] <;> rfl
          | inputDataWordBE? offset =>
              simp [handler, handleRequest] <;> rfl
          | callContractWord target input =>
              simp [handler, handleRequest] <;> rfl
          | callContractWordWithValue target value input =>
              simp [handler, handleRequest] <;> rfl
          | createContractWord templateId value input =>
              simp [handler, handleRequest] <;> rfl
          | emitLogWord topic payload =>
              simp [handler, handleRequest] <;> rfl)
        context fuel state
  simpa only [run_storageAddress, if_neg different] using preserved

end Solcore.ContractRuntime.HostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverSafetyProperties`
-/

/-! Type and fault safety for the canonical storage host driver. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostStorageDriver

theorem run_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome.HasType
      resultType definitions := by
  simpa only [run] using
    HostDriver.run_hasType
      (@handler RollbackState TraceState inputs)
      context fuel state stateTyping

theorem run_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome ≠
      .fault error faultState := by
  simpa only [run] using
    HostDriver.run_ne_fault
      (@handler RollbackState TraceState inputs)
      context fuel state faultState error stateTyping

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorage_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithStorage context inputs fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions := by
  exact HostStorageDriver.run_hasType
    context inputs fuel _ code.initialState_hasType

theorem runWithStorage_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithStorage context inputs fuel).outcome ≠
      .fault error faultState := by
  exact HostStorageDriver.run_ne_fault
    context inputs fuel _ faultState error code.initialState_hasType

theorem runWithStorage_done_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (result :
      (code.runWithStorage context inputs fuel).outcome =
        .done value store) :
    ∃ world,
      Core.HostStoreHasTypes world store code.program.dataDefinitions ∧
        Core.HostRuntimeValueHasType world value code.program.resultType
          code.program.dataDefinitions := by
  have typing := code.runWithStorage_hasType context inputs fuel
  rw [result] at typing
  exact typing

theorem runWithStorage_outOfFuel_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {state : Core.State}
    (result :
      (code.runWithStorage context inputs fuel).outcome =
        .outOfFuel state) :
    Core.HostStateHasType state code.program.resultType
      code.program.dataDefinitions := by
  have typing := code.runWithStorage_hasType context inputs fuel
  rw [result] at typing
  exact typing

end CheckedHostCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverFuelProperties`
-/

/-! Whole-run fuel accounting indexed by immutable execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostStorageDriver

/-- Handled transition segments under one exact immutable input. -/
abbrev HandledSteps
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs) :=
  HostDriver.HandledSteps
    (@handler RollbackState TraceState inputs)

/-- Fuel soundness indexed by one exact immutable input. -/
def FuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (result : HostDriverResult (Context RollbackState TraceState))
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (startContext : Context RollbackState TraceState)
    (start : Core.State) : Prop :=
  result.FuelSoundWith
    (@handler RollbackState TraceState inputs)
    fuel startContext start

namespace FuelSound

/-- Prefix a sound suffix with one request handled under the same input. -/
theorem prependRequest
    {RollbackState : Type u} {TraceState : Type v}
    {inputs : ExecutionInputs}
    {result : HostDriverResult (Context RollbackState TraceState)}
    {fuel remainingFuel prefixSteps : Nat}
    {context nextContext : Context RollbackState TraceState}
    {start requestState resumed : Core.State}
    {suspension : Core.HostSuspension}
    (prefixPath : Core.HostSteps prefixSteps start requestState)
    (emission : Core.HostRequestEmission requestState suspension)
    (supported :
      (@handler RollbackState TraceState inputs).supports
        suspension.request = true)
    (handled :
      handleSuspension inputs context suspension =
        (nextContext, resumed))
    (accounting : prefixSteps + remainingFuel + 1 = fuel)
    (suffixSound :
      HostStorageDriver.FuelSound
        result inputs remainingFuel nextContext resumed) :
    HostStorageDriver.FuelSound
      result inputs fuel context start := by
  apply HostDriverResult.FuelSoundWith.prependRequest
    prefixPath emission supported (accounting := accounting)
  · simpa only [handleSuspension] using handled
  · exact suffixSound

end FuelSound

theorem run_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    FuelSound (run context inputs fuel state) inputs
      fuel context state := by
  simpa only [run, FuelSound] using
    HostDriver.run_fuelSound
      (@handler RollbackState TraceState inputs)
      context fuel state

theorem run_eq_of_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState))
    (sound : FuelSound result inputs fuel context state) :
    run context inputs fuel state = result := by
  simpa only [run, FuelSound] using
    HostDriver.run_eq_of_fuelSoundWith
      (@handler RollbackState TraceState inputs)
      context fuel state result sound

theorem run_eq_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState)) :
    run context inputs fuel state = result ↔
      FuelSound result inputs fuel context state := by
  simpa only [run, FuelSound] using
    HostDriver.run_eq_iff_fuelSoundWith
      (@handler RollbackState TraceState inputs)
      context fuel state result

/-- Exhausted storage execution resumes under the exact same immutable input. -/
theorem run_additional_of_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context nextContext : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel additional : Nat)
    (state exhausted : Core.State)
    (execution :
      run context inputs fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    run context inputs (fuel + additional) state =
      run nextContext inputs additional exhausted := by
  simpa only [run] using
    HostDriver.run_additional_of_outOfFuel
      (@handler RollbackState TraceState inputs) execution

/-- Split storage execution agrees with one summed-budget run. -/
theorem resumeWithFuel_run
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel additional : Nat)
    (state : Core.State) :
    (run context inputs fuel state).resumeWithFuel
        (@handler RollbackState TraceState inputs) additional =
      run context inputs (fuel + additional) state := by
  simpa only [run] using
    HostDriverResult.resumeWithFuel_run
      (@handler RollbackState TraceState inputs)
      context fuel additional state

theorem run_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    {fuel largerFuel : Nat}
    (state : Core.State)
    {finalContext : Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      run context inputs fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    run context inputs largerFuel state =
      ⟨finalContext, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_done_stable
      (@handler RollbackState TraceState inputs)
      execution more

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorage_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostStorageDriver.FuelSound
      (code.runWithStorage context inputs fuel) inputs fuel context
      (Core.State.initial code.program.body Core.hostEnvironment) := by
  exact HostStorageDriver.run_fuelSound context inputs fuel _

theorem runWithStorage_eq_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState)) :
    code.runWithStorage context inputs fuel = result ↔
      HostStorageDriver.FuelSound result inputs fuel context
        (Core.State.initial code.program.body Core.hostEnvironment) := by
  simpa only [runWithStorage] using
    HostStorageDriver.run_eq_iff_fuelSound context inputs fuel
      (Core.State.initial code.program.body Core.hostEnvironment) result

theorem runWithStorage_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext : HostStorageDriver.Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithStorage context inputs largerFuel =
      ⟨finalContext, .done value store⟩ := by
  simpa only [runWithStorage] using
    HostStorageDriver.run_done_stable context inputs
      (Core.State.initial code.program.body Core.hostEnvironment)
      execution more

/-- Checked storage execution has the same exact split-fuel law. -/
theorem runWithStorage_resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional =
      code.runWithStorage context inputs (fuel + additional) := by
  simpa only [runWithStorage] using
    HostStorageDriver.resumeWithFuel_run context inputs fuel additional
      (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.ContractRuntime
