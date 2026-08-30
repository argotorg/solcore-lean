import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteCodeProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWriteIsolationProperties
import Solcore.Semantics.CheckedHostCoreProgramProperties
import Solcore.Semantics.HostDriverProperties
import Solcore.Semantics.TransactionHostStorageDriver
import Solcore.Semantics.TransactionHostStorageHandlerProperties

/-! Execution, preservation, and safety laws for transaction storage runs. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace TransactionHostStorageDriver

@[simp] theorem run_of_done
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    run context inputs fuel state = ⟨context, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_of_done (handler inputs)
      context fuel state value store execution

@[simp] theorem run_of_outOfFuel
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run context inputs fuel state = ⟨context, .outOfFuel exhausted⟩ := by
  simpa only [run] using
    HostDriver.run_of_outOfFuel (handler inputs)
      context fuel state exhausted execution

@[simp] theorem run_of_fault
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run context inputs fuel state =
      ⟨context, .fault error faultState⟩ := by
  simpa only [run] using
    HostDriver.run_of_fault (handler inputs)
      context fuel state faultState error execution

theorem run_of_suspended
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    run context inputs fuel state =
      run (handleSuspension inputs context suspension).1 inputs remainingFuel
        (handleSuspension inputs context suspension).2 := by
  simpa only [run, handleSuspension] using
    (HostDriver.run_of_suspended (handler inputs)
      context fuel remainingFuel state suspension execution
      |>.trans (by rw [if_pos (handler_supports inputs suspension.request)]))

theorem run_of_suspended_emitLogWord
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
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
      run (context.recordLog (wordLog inputs topic payload)) inputs
        remainingFuel ⟨.ret .unit, continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.emitLogWord topic payload, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.emitLogWord topic payload, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_emitLogWord]

@[simp] theorem run_storageAddress
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.storageAddress =
      context.context.storageAddress := by
  simpa only [run] using
    HostDriver.run_observe (handler inputs)
      (fun current => current.context.storageAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest, HostStorageDriver.handleRequest])
      context fuel state

@[simp] theorem run_checkpoint
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.values.checkpoint =
      context.context.values.checkpoint := by
  simpa only [run] using
    HostDriver.run_observe (handler inputs)
      (fun current => current.context.values.checkpoint)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest, HostStorageDriver.handleRequest])
      context fuel state

@[simp] theorem run_trace
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.values.working.2.trace =
      context.context.values.working.2.trace := by
  exact Subsingleton.elim _ _

@[simp] theorem run_workingCode?
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address) :
    (run context inputs fuel state).context.context.values.working.1.code?
        observedAddress =
      context.context.values.working.1.code? observedAddress := by
  simpa only [run] using
    HostDriver.run_observe (handler inputs)
      (fun current =>
        current.context.values.working.1.code? observedAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest, HostStorageDriver.handleRequest])
      context fuel state

@[simp] theorem run_workingAccount?_of_ne_storageAddress
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
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
      HostDriver.run_observe (handler inputs)
        (fun current =>
          if observedAddress = current.context.storageAddress
            then none
            else current.context.values.working.1.account? observedAddress)
        (by
          intro current request
          cases request with
          | storageWrite slot value =>
              by_cases same :
                  observedAddress = current.context.storageAddress
              · simp [handler, handleRequest,
                  HostStorageDriver.handleRequest, same]
              · simp [handler, handleRequest,
                  HostStorageDriver.handleRequest, same]
          | storageRead slot =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | storageAddress =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | codeAddress =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | callValue =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | callerAddress =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | inputDataByte? offset =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | inputDataSize =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | inputDataWordBE? offset =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | currentAddress =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | callContractWord target input =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | callContractWordWithValue target value input =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | createContractWord templateId value input =>
              simp [handler, handleRequest, HostStorageDriver.handleRequest]
          | emitLogWord topic payload =>
              simp [handler, handleRequest])
        context fuel state
  simpa only [run_storageAddress, if_neg different] using preserved

theorem run_hasType
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome.HasType
      resultType definitions := by
  simpa only [run] using
    HostDriver.run_hasType (handler inputs)
      context fuel state stateTyping

theorem run_ne_fault
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome ≠
      .fault error faultState := by
  simpa only [run] using
    HostDriver.run_ne_fault (handler inputs)
      context fuel state faultState error stateTyping

/-- The transaction policy supports every request, including logs. -/
theorem run_ne_unsupported
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    (run context inputs fuel state).outcome ≠
      .unsupported suspension remainingFuel := by
  simpa only [run] using
    HostDriver.run_ne_unsupported_of_supports_all
      (handler inputs) (handler_supports inputs) context fuel state
      suspension remainingFuel

end TransactionHostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithTransactionStorage_hasType
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithTransactionStorage context inputs fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions := by
  exact TransactionHostStorageDriver.run_hasType
    context inputs fuel _ code.initialState_hasType

theorem runWithTransactionStorage_ne_fault
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithTransactionStorage context inputs fuel).outcome ≠
      .fault error faultState := by
  exact TransactionHostStorageDriver.run_ne_fault
    context inputs fuel _ faultState error code.initialState_hasType

theorem runWithTransactionStorage_ne_unsupported
    (code : CheckedHostCoreProgram)
    (context : TransactionHostStorageDriver.Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (suspension : Core.HostSuspension)
    (remainingFuel : Nat) :
    (code.runWithTransactionStorage context inputs fuel).outcome ≠
      .unsupported suspension remainingFuel := by
  exact TransactionHostStorageDriver.run_ne_unsupported
    context inputs fuel _ suspension remainingFuel

end CheckedHostCoreProgram

end Solcore.Semantics
