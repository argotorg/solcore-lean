import Solcore.Semantics.AddressWordBridgeProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWritePresenceProperties
import Solcore.Semantics.HostDriverProperties
import Solcore.Semantics.HostStorageExecutionInputsProperties
import Solcore.Semantics.HostStorageHandlerWithExecutionInputs

/-! Exact current-request laws for the explicit-input storage handler seam. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

universe u v

@[simp] theorem handleRequestWithInputs_storageRead
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    handleRequestWithInputs inputs context (.storageRead slot) =
      (context, context.readStorage slot) :=
  rfl

@[simp] theorem handleSuspensionWithInputs_storageRead
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspensionWithInputs inputs context
        ⟨.storageRead slot, continuation, store⟩ =
      (context,
        ⟨.ret (.word (context.readStorage slot)), continuation, store⟩) :=
  rfl

@[simp] theorem handleRequestWithInputs_storageWrite
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    handleRequestWithInputs inputs context (.storageWrite slot value) =
      (context.writeStorage slot value, ()) :=
  rfl

@[simp] theorem handleSuspensionWithInputs_storageWrite
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspensionWithInputs inputs context
        ⟨.storageWrite slot value, continuation, store⟩ =
      (context.writeStorage slot value,
        ⟨.ret .unit, continuation, store⟩) :=
  rfl

@[simp] theorem handleRequestWithInputs_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequestWithInputs inputs context .storageAddress =
      (context, addressToWord context.context.storageAddress) :=
  rfl

@[simp] theorem handleSuspensionWithInputs_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspensionWithInputs inputs context
        ⟨.storageAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequestWithInputs_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequestWithInputs inputs context .codeAddress =
      (context, addressToWord inputs.codeAddress) :=
  rfl

@[simp] theorem handleSuspensionWithInputs_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspensionWithInputs inputs context
        ⟨.codeAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord inputs.codeAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleSuspensionWithInputs_storageRead_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageRead slot, continuation, store⟩).1 = context := by
  rw [handleSuspensionWithInputs_storageRead]

@[simp] theorem handleSuspensionWithInputs_storageWrite_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageWrite slot value, continuation, store⟩).1 =
        context.writeStorage slot value := by
  rw [handleSuspensionWithInputs_storageWrite]

@[simp] theorem handleSuspensionWithInputs_storageWrite_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.control =
        .ret .unit := by
  rw [handleSuspensionWithInputs_storageWrite]

@[simp] theorem handleSuspensionWithInputs_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspensionWithInputs inputs context suspension).2.continuation =
      suspension.continuation := by
  simp [handleSuspensionWithInputs, HostHandler.handleSuspension]

@[simp] theorem handleSuspensionWithInputs_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspensionWithInputs inputs context suspension).2.store =
      suspension.store := by
  simp [handleSuspensionWithInputs, HostHandler.handleSuspension]

@[simp] theorem handleSuspensionWithInputs_storageWrite_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspensionWithInputs_continuation inputs context _

@[simp] theorem handleSuspensionWithInputs_storageWrite_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.store = store := by
  exact handleSuspensionWithInputs_store inputs context _

@[simp] theorem handleSuspensionWithInputs_storageAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageAddress, continuation, store⟩).1 = context := by
  rw [handleSuspensionWithInputs_storageAddress]

@[simp] theorem handleSuspensionWithInputs_storageAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord context.context.storageAddress)) := by
  rw [handleSuspensionWithInputs_storageAddress]

@[simp] theorem handleSuspensionWithInputs_storageAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspensionWithInputs_continuation inputs context _

@[simp] theorem handleSuspensionWithInputs_storageAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.storageAddress, continuation, store⟩).2.store = store := by
  exact handleSuspensionWithInputs_store inputs context _

@[simp] theorem handleSuspensionWithInputs_codeAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.codeAddress, continuation, store⟩).1 = context := by
  rw [handleSuspensionWithInputs_codeAddress]

@[simp] theorem handleSuspensionWithInputs_codeAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.codeAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord inputs.codeAddress)) := by
  rw [handleSuspensionWithInputs_codeAddress]

@[simp] theorem handleSuspensionWithInputs_codeAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.codeAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspensionWithInputs_continuation inputs context _

@[simp] theorem handleSuspensionWithInputs_codeAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspensionWithInputs inputs context
      ⟨.codeAddress, continuation, store⟩).2.store = store := by
  exact handleSuspensionWithInputs_store inputs context _

@[simp] theorem wordToAddress?_handlerWithInputs_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress?
        ((handlerWithInputs inputs).handle context .storageAddress).2 =
      some context.context.storageAddress := by
  change wordToAddress? (addressToWord context.context.storageAddress) = _
  exact wordToAddress?_addressToWord context.context.storageAddress

@[simp] theorem wordToAddress?_handlerWithInputs_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress? ((handlerWithInputs inputs).handle context .codeAddress).2 =
      some inputs.codeAddress := by
  change wordToAddress? (addressToWord inputs.codeAddress) = _
  exact wordToAddress?_addressToWord inputs.codeAddress

@[simp] theorem handlerWithInputs_storageWrite_readStorage_same
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    (((handlerWithInputs inputs).handle context
      (.storageWrite slot value)).1).readStorage slot = value := by
  change (context.writeStorage slot value).readStorage slot = value
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
      context slot value

@[simp] theorem handlerWithInputs_storageWrite_zero_storageValue?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    (((handlerWithInputs inputs).handle context
      (.storageWrite slot Core.Word.zero)).1).storageAccount.storageValue?
        slot = none := by
  change
    (context.writeStorage slot Core.Word.zero).storageAccount.storageValue?
      slot = none
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_zero
      context slot

theorem handleSuspensionWithInputs_state_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension)
    (typing : Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handleSuspensionWithInputs inputs context suspension).2
      resultType definitions := by
  simpa only [handleSuspensionWithInputs] using
    HostHandler.handleSuspension_state_hasType
      (handlerWithInputs inputs) context suspension typing

end Solcore.Semantics.HostStorageDriver
