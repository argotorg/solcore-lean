import Solcore.Semantics.AddressWordBridge
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.Semantics.HostDriver

/-! Combined interpretation of Core storage requests through working storage. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

/-- The proven-present working-storage context threaded by the storage driver. -/
abbrev Context
    (RollbackState : Type u)
    (TraceState : Type v) :=
  FrameCheckpointedWorkingPairWithPresentStorageAccount
    RollbackState TraceState

/--
Interpret one storage request and return the next context together with the
response indexed by that exact request.
-/
def handleRequest
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (request : Core.HostRequest) :
    Context RollbackState TraceState × request.Response :=
  match request with
  | .storageRead slot => (context, context.readStorage slot)
  | .storageWrite slot value => (context.writeStorage slot value, ())
  | .storageAddress =>
      (context, addressToWord context.context.storageAddress)

/-- The total dependent handler used by combined storage execution. -/
def handler
    {RollbackState : Type u}
    {TraceState : Type v} :
    HostHandler (Context RollbackState TraceState) where
  handle := handleRequest

/-- Handle one storage suspension and resume its saved Core continuation. -/
def handleSuspension
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    Context RollbackState TraceState × Core.State :=
  handler.handleSuspension context suspension

@[simp] theorem handleRequest_storageRead
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    handleRequest context (.storageRead slot) =
      (context, context.readStorage slot) :=
  rfl

@[simp] theorem handleSuspension_storageRead
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (slot : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension context
        ⟨.storageRead slot, continuation, store⟩ =
      (context,
        ⟨.ret (.word (context.readStorage slot)), continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_storageWrite
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    handleRequest context (.storageWrite slot value) =
      (context.writeStorage slot value, ()) :=
  rfl

@[simp] theorem handleSuspension_storageWrite
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension context
        ⟨.storageWrite slot value, continuation, store⟩ =
      (context.writeStorage slot value,
        ⟨.ret .unit, continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState) :
    handleRequest context .storageAddress =
      (context, addressToWord context.context.storageAddress) :=
  rfl

@[simp] theorem handleSuspension_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension context
        ⟨.storageAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩) :=
  rfl

end HostStorageDriver

end Solcore.Semantics
