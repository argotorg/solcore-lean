import Solcore.Semantics.AddressWordBridgeProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWritePresenceProperties
import Solcore.Semantics.HostDriverProperties
import Solcore.Semantics.HostStorageExecutionInputsProperties
import Solcore.Semantics.HostStorageHandler

/-! Exact request laws for the canonical storage host handler. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

universe u v

@[simp] theorem handleRequest_storageRead
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    handleRequest inputs context (.storageRead slot) =
      (context, context.readStorage slot) :=
  rfl

@[simp] theorem handleSuspension_storageRead
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.storageRead slot, continuation, store⟩ =
      (context,
        ⟨.ret (.word (context.readStorage slot)), continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_storageWrite
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    handleRequest inputs context (.storageWrite slot value) =
      (context.writeStorage slot value, ()) :=
  rfl

@[simp] theorem handleSuspension_storageWrite
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.storageWrite slot value, continuation, store⟩ =
      (context.writeStorage slot value,
        ⟨.ret .unit, continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .storageAddress =
      (context, addressToWord context.context.storageAddress) :=
  rfl

@[simp] theorem handleSuspension_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .codeAddress =
      (context, addressToWord inputs.codeAddress) :=
  rfl

@[simp] theorem handleSuspension_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord inputs.codeAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_callValue
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .callValue =
      (context, inputs.callValue) :=
  rfl

@[simp] theorem handleSuspension_callValue
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.callValue, continuation, store⟩ =
      (context,
        ⟨.ret (.word inputs.callValue), continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_callerAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .callerAddress =
      (context, addressToWord inputs.callerAddress) :=
  rfl

@[simp] theorem handleSuspension_callerAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.callerAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord inputs.callerAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_inputDataByte?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word) :
    handleRequest inputs context (.inputDataByte? offset) =
      (context, inputs.inputData.byte? offset) :=
  rfl

@[simp] theorem handleSuspension_inputDataByte?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.inputDataByte? offset, continuation, store⟩ =
      (context,
        (Core.HostSuspension.mk (.inputDataByte? offset) continuation store).resume
          (inputs.inputData.byte? offset)) :=
  rfl

theorem handleSuspension_inputDataByte?_none
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (absent : inputs.inputData.byte? offset = none) :
    handleSuspension inputs context
        ⟨.inputDataByte? offset, continuation, store⟩ =
      (context,
        ⟨.ret (.inLeft .word .unit), continuation, store⟩) := by
  rw [handleSuspension_inputDataByte?, absent]
  rfl

theorem handleSuspension_inputDataByte?_some
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset byte : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (present : inputs.inputData.byte? offset = some byte) :
    handleSuspension inputs context
        ⟨.inputDataByte? offset, continuation, store⟩ =
      (context,
        ⟨.ret (.inRight .unit (.word byte)), continuation, store⟩) := by
  rw [handleSuspension_inputDataByte?, present]
  rfl

@[simp] theorem handleSuspension_storageRead_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageRead slot, continuation, store⟩).1 = context := by
  rw [handleSuspension_storageRead]

@[simp] theorem handleSuspension_storageWrite_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageWrite slot value, continuation, store⟩).1 =
        context.writeStorage slot value := by
  rw [handleSuspension_storageWrite]

@[simp] theorem handleSuspension_storageWrite_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.control =
        .ret .unit := by
  rw [handleSuspension_storageWrite]

@[simp] theorem handleSuspension_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspension inputs context suspension).2.continuation =
      suspension.continuation := by
  simp [handleSuspension, HostHandler.handleSuspension]

@[simp] theorem handleSuspension_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspension inputs context suspension).2.store =
      suspension.store := by
  simp [handleSuspension, HostHandler.handleSuspension]

@[simp] theorem handleSuspension_storageWrite_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_storageWrite_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_storageAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageAddress, continuation, store⟩).1 = context := by
  rw [handleSuspension_storageAddress]

@[simp] theorem handleSuspension_storageAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord context.context.storageAddress)) := by
  rw [handleSuspension_storageAddress]

@[simp] theorem handleSuspension_storageAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_storageAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageAddress, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_codeAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.codeAddress, continuation, store⟩).1 = context := by
  rw [handleSuspension_codeAddress]

@[simp] theorem handleSuspension_codeAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.codeAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord inputs.codeAddress)) := by
  rw [handleSuspension_codeAddress]

@[simp] theorem handleSuspension_codeAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.codeAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_codeAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.codeAddress, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_callValue_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callValue, continuation, store⟩).1 = context := by
  rw [handleSuspension_callValue]

@[simp] theorem handleSuspension_callValue_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callValue, continuation, store⟩).2.control =
        .ret (.word inputs.callValue) := by
  rw [handleSuspension_callValue]

@[simp] theorem handleSuspension_callValue_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callValue, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_callValue_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callValue, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_callerAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callerAddress, continuation, store⟩).1 = context := by
  rw [handleSuspension_callerAddress]

@[simp] theorem handleSuspension_callerAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callerAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord inputs.callerAddress)) := by
  rw [handleSuspension_callerAddress]

@[simp] theorem handleSuspension_callerAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callerAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_callerAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callerAddress, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_inputDataByte?_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).1 = context := by
  rw [handleSuspension_inputDataByte?]

theorem handleSuspension_inputDataByte?_context_independent
    {RollbackState : Type u} {TraceState : Type v}
    (leftInputs rightInputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension leftInputs context
        ⟨.inputDataByte? offset, continuation, store⟩).1 =
      (handleSuspension rightInputs context
        ⟨.inputDataByte? offset, continuation, store⟩).1 := by
  simp

@[simp] theorem handleSuspension_inputDataByte?_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
  (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.control =
        .ret ((Core.HostRequest.inputDataByte? offset).responseValue
          (inputs.inputData.byte? offset)) := by
  rw [handleSuspension_inputDataByte?]
  rfl

theorem handleSuspension_inputDataByte?_control_none
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store)
    (absent : inputs.inputData.byte? offset = none) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.control =
        .ret (.inLeft .word .unit) := by
  rw [handleSuspension_inputDataByte?_none inputs context offset continuation store
    absent]

theorem handleSuspension_inputDataByte?_control_some
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset byte : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store)
    (present : inputs.inputData.byte? offset = some byte) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.control =
        .ret (.inRight .unit (.word byte)) := by
  rw [handleSuspension_inputDataByte?_some inputs context offset byte continuation
    store present]

@[simp] theorem handleSuspension_inputDataByte?_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_inputDataByte?_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem wordToAddress?_handler_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress?
        ((handler inputs).handle context .storageAddress).2 =
      some context.context.storageAddress := by
  change wordToAddress? (addressToWord context.context.storageAddress) = _
  exact wordToAddress?_addressToWord context.context.storageAddress

@[simp] theorem wordToAddress?_handler_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress? ((handler inputs).handle context .codeAddress).2 =
      some inputs.codeAddress := by
  change wordToAddress? (addressToWord inputs.codeAddress) = _
  exact wordToAddress?_addressToWord inputs.codeAddress

@[simp] theorem wordToAddress?_handler_callerAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress? ((handler inputs).handle context .callerAddress).2 =
      some inputs.callerAddress := by
  change wordToAddress? (addressToWord inputs.callerAddress) = _
  exact wordToAddress?_addressToWord inputs.callerAddress

@[simp] theorem handler_storageWrite_readStorage_same
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    (((handler inputs).handle context
      (.storageWrite slot value)).1).readStorage slot = value := by
  change (context.writeStorage slot value).readStorage slot = value
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
      context slot value

@[simp] theorem handler_storageWrite_zero_storageValue?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    (((handler inputs).handle context
      (.storageWrite slot Core.Word.zero)).1).storageAccount.storageValue?
        slot = none := by
  change
    (context.writeStorage slot Core.Word.zero).storageAccount.storageValue?
      slot = none
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_zero
      context slot

theorem handleSuspension_state_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension)
    (typing : Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handleSuspension inputs context suspension).2
      resultType definitions := by
  simpa only [handleSuspension] using
    HostHandler.handleSuspension_state_hasType
      (handler inputs) context suspension typing

end Solcore.Semantics.HostStorageDriver
