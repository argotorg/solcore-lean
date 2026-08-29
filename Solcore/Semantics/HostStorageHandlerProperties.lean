import Solcore.Semantics.AddressWordBridgeProperties
import Solcore.Semantics.HostDriverProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageReadWriteProperties
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWritePresenceProperties
import Solcore.Semantics.HostStorageHandler

/-! Exact read/write behavior and safety of the combined storage handler. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

universe u v

/-- A handled read leaves the complete storage context unchanged. -/
@[simp] theorem handleSuspension_storageRead_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageRead slot, continuation, store⟩).1 = context := by
  rw [handleSuspension_storageRead]

/-- A handled write returns exactly the existing total-write context. -/
@[simp] theorem handleSuspension_storageWrite_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageWrite slot value, continuation, store⟩).1 =
        context.writeStorage slot value := by
  rw [handleSuspension_storageWrite]

/-- A handled write resumes Core with the dependent Unit response. -/
@[simp] theorem handleSuspension_storageWrite_control
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageWrite slot value, continuation, store⟩).2.control =
        .ret .unit := by
  rw [handleSuspension_storageWrite]

/-- Handling any storage request preserves the saved Core continuation. -/
@[simp] theorem handleSuspension_continuation
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspension codeAddress context suspension).2.continuation =
      suspension.continuation := by
  simp [handleSuspension, HostHandler.handleSuspension]

/-- Handling any storage request preserves the Core-local store. -/
@[simp] theorem handleSuspension_store
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspension codeAddress context suspension).2.store = suspension.store := by
  simp [handleSuspension, HostHandler.handleSuspension]

/-- The write branch preserves the exact saved Core continuation. -/
@[simp] theorem handleSuspension_storageWrite_continuation
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageWrite slot value, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation codeAddress context
    ⟨Core.HostRequest.storageWrite slot value, continuation, store⟩

/-- The write branch preserves the exact Core-local store. -/
@[simp] theorem handleSuspension_storageWrite_store
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageWrite slot value, continuation, store⟩).2.store = store := by
  exact handleSuspension_store codeAddress context
    ⟨Core.HostRequest.storageWrite slot value, continuation, store⟩

/-- A handled selector observation leaves the complete context unchanged. -/
@[simp] theorem handleSuspension_storageAddress_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageAddress, continuation, store⟩).1 = context := by
  rw [handleSuspension_storageAddress]

/-- A selector observation resumes Core with its exact widened Word. -/
@[simp] theorem handleSuspension_storageAddress_control
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord context.context.storageAddress)) := by
  rw [handleSuspension_storageAddress]

/-- A selector observation preserves the exact saved Core continuation. -/
@[simp] theorem handleSuspension_storageAddress_continuation
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation codeAddress context
    ⟨Core.HostRequest.storageAddress, continuation, store⟩

/-- A selector observation preserves the exact Core-local store. -/
@[simp] theorem handleSuspension_storageAddress_store
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension codeAddress context
      ⟨.storageAddress, continuation, store⟩).2.store = store := by
  exact handleSuspension_store codeAddress context
    ⟨Core.HostRequest.storageAddress, continuation, store⟩

/-- The widened handler response narrows back to the retained selector. -/
@[simp] theorem wordToAddress?_handler_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState) :
    wordToAddress? ((handler codeAddress).handle context .storageAddress).2 =
      some context.context.storageAddress := by
  change
    wordToAddress? (addressToWord context.context.storageAddress) =
      some context.context.storageAddress
  exact wordToAddress?_addressToWord context.context.storageAddress

/-- Reading the slot updated by the dependent handler observes its new value. -/
@[simp] theorem handler_storageWrite_readStorage_same
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    (((handler codeAddress).handle context
      (.storageWrite slot value)).1).readStorage slot =
      value := by
  change (context.writeStorage slot value).readStorage slot = value
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
      context slot value

/-- A zero write through the handler removes the selected sparse entry. -/
@[simp] theorem handler_storageWrite_zero_storageValue?
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    (((handler codeAddress).handle context
      (.storageWrite slot Core.Word.zero)).1).storageAccount.storageValue?
        slot = none := by
  change
    (context.writeStorage slot Core.Word.zero).storageAccount.storageValue?
      slot = none
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_zero
      context slot

/-- The dependent response supplied by the storage handler resumes safely. -/
theorem handleSuspension_state_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension)
    (typing :
      Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handleSuspension codeAddress context suspension).2
      resultType definitions := by
  simpa only [handleSuspension] using
    HostHandler.handleSuspension_state_hasType
      (handler codeAddress) context suspension typing

end Solcore.Semantics.HostStorageDriver
