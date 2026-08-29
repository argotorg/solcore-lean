import Solcore.Semantics.HostDriverProperties
import Solcore.Semantics.HostStorageHandler

/-! Exact read behavior and safety of the combined storage handler. -/

set_option autoImplicit false

namespace Solcore.Semantics.HostStorageDriver

universe u v

/-- A handled read leaves the complete storage context unchanged. -/
@[simp] theorem handleSuspension_storageRead_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (slot : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension context
      ⟨.storageRead slot, continuation, store⟩).1 = context := by
  rw [handleSuspension_storageRead]

/-- Handling any storage request preserves the saved Core continuation. -/
@[simp] theorem handleSuspension_continuation
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspension context suspension).2.continuation =
      suspension.continuation := by
  simp [handleSuspension, HostHandler.handleSuspension]

/-- Handling any storage request preserves the Core-local store. -/
@[simp] theorem handleSuspension_store
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspension context suspension).2.store = suspension.store := by
  simp [handleSuspension, HostHandler.handleSuspension]

/-- The dependent response supplied by the storage handler resumes safely. -/
theorem handleSuspension_state_hasType
    {RollbackState : Type u}
    {TraceState : Type v}
    {definitions : Core.DataEnvironment}
    {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension)
    (typing :
      Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handleSuspension context suspension).2
      resultType definitions := by
  simpa only [handleSuspension] using
    HostHandler.handleSuspension_state_hasType
      handler context suspension typing

end Solcore.Semantics.HostStorageDriver
