import Solcore.Semantics.HostStorageHandlerProperties
import Solcore.Semantics.TransactionHostStorageContextProperties
import Solcore.Semantics.TransactionHostStorageHandler

/-! Exact emission and compatibility laws for the transaction host handler. -/

set_option autoImplicit false

namespace Solcore.Semantics.TransactionHostStorageDriver

@[simp] theorem handler_supports
    (inputs : HostStorageDriver.ExecutionInputs)
    (request : Core.HostRequest) :
    (handler inputs).supports request = true :=
  rfl

/-- Every non-log request is delegated to the canonical storage handler. -/
theorem handleRequest_eq_generic_of_not_emitLogWord
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (request : Core.HostRequest)
    (notEmission :
      ∀ topic payload, request ≠ .emitLogWord topic payload) :
    handleRequest inputs context request =
      HostStorageDriver.handleRequest inputs context request := by
  cases request <;> simp_all [handleRequest]

@[simp] theorem handleRequest_emitLogWord
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    handleRequest inputs context (.emitLogWord topic payload) =
      (context.recordLog (wordLog inputs topic payload), ()) :=
  rfl

@[simp] theorem handleSuspension_emitLogWord
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.emitLogWord topic payload, continuation, store⟩ =
      (context.recordLog (wordLog inputs topic payload),
        ⟨.ret .unit, continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_emitLogWord_logList
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (Context.workingJournal
      (handleRequest inputs context (.emitLogWord topic payload)).1).logList =
      context.workingJournal.logList ++ [wordLog inputs topic payload] := by
  simp

@[simp] theorem handleRequest_emitLogWord_createdContractList
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    TransactionJournal.createdContractList
      (Context.workingJournal
        (handleRequest inputs context (.emitLogWord topic payload)).1) =
      context.workingJournal.createdContractList := by
  simp

@[simp] theorem handleRequest_emitLogWord_workingWorld
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (handleRequest inputs context
      (.emitLogWord topic payload)).1.context.values.working.1 =
      context.context.values.working.1 := by
  simp

@[simp] theorem handleRequest_emitLogWord_storageAccount
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (handleRequest inputs context
      (.emitLogWord topic payload)).1.storageAccount = context.storageAccount := by
  simp

@[simp] theorem handleRequest_emitLogWord_storageAddress
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (handleRequest inputs context
      (.emitLogWord topic payload)).1.context.storageAddress =
        context.context.storageAddress := by
  simp

@[simp] theorem handleRequest_emitLogWord_checkpoint
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word) :
    (handleRequest inputs context
      (.emitLogWord topic payload)).1.context.values.checkpoint =
        context.context.values.checkpoint := by
  simp

@[simp] theorem handleSuspension_emitLogWord_control
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.emitLogWord topic payload, continuation, store⟩).2.control =
        .ret .unit := by
  simp

@[simp] theorem handleSuspension_emitLogWord_continuation
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.emitLogWord topic payload, continuation, store⟩).2.continuation =
        continuation := by
  simp

@[simp] theorem handleSuspension_emitLogWord_store
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.emitLogWord topic payload, continuation, store⟩).2.store = store := by
  simp

theorem handleSuspension_state_hasType
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (inputs : HostStorageDriver.ExecutionInputs)
    (context : Context)
    (suspension : Core.HostSuspension)
    (typing : Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handleSuspension inputs context suspension).2 resultType definitions := by
  simpa only [handleSuspension] using
    HostHandler.handleSuspension_state_hasType
      (handler inputs) context suspension typing

end Solcore.Semantics.TransactionHostStorageDriver
