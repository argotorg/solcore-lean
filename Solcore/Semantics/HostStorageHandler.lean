import Solcore.Semantics.AddressWordBridge
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageWrite
import Solcore.Semantics.HostDriver
import Solcore.Semantics.HostStorageContext

/-! Combined interpretation of supported Core host requests during storage execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

namespace HostStorageDriver

/--
Interpret one supported host request and return the next context together with
the response indexed by that exact request.
-/
def handleRequest
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (request : Core.HostRequest) :
    Context RollbackState TraceState × request.Response :=
  match request with
  | .storageRead slot => (context, context.readStorage slot)
  | .storageWrite slot value => (context.writeStorage slot value, ())
  | .storageAddress =>
      (context, addressToWord context.context.storageAddress)
  | .codeAddress => (context, addressToWord codeAddress)

/-- The total dependent handler used by combined storage execution. -/
def handler
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address) :
    HostHandler (Context RollbackState TraceState) where
  handle := handleRequest codeAddress

/-- Handle one supported host suspension and resume its saved Core continuation. -/
def handleSuspension
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    Context RollbackState TraceState × Core.State :=
  (handler codeAddress).handleSuspension context suspension

@[simp] theorem handleRequest_storageRead
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    handleRequest codeAddress context (.storageRead slot) =
      (context, context.readStorage slot) :=
  rfl

@[simp] theorem handleSuspension_storageRead
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension codeAddress context
        ⟨.storageRead slot, continuation, store⟩ =
      (context,
        ⟨.ret (.word (context.readStorage slot)), continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_storageWrite
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    handleRequest codeAddress context (.storageWrite slot value) =
      (context.writeStorage slot value, ()) :=
  rfl

@[simp] theorem handleSuspension_storageWrite
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension codeAddress context
        ⟨.storageWrite slot value, continuation, store⟩ =
      (context.writeStorage slot value,
        ⟨.ret .unit, continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState) :
    handleRequest codeAddress context .storageAddress =
      (context, addressToWord context.context.storageAddress) :=
  rfl

@[simp] theorem handleSuspension_storageAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension codeAddress context
        ⟨.storageAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_codeAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState) :
    handleRequest codeAddress context .codeAddress =
      (context, addressToWord codeAddress) :=
  rfl

@[simp] theorem handleSuspension_codeAddress
    {RollbackState : Type u}
    {TraceState : Type v}
    (codeAddress : Address)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension codeAddress context
        ⟨.codeAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord codeAddress)), continuation, store⟩) :=
  rfl

end HostStorageDriver

end Solcore.Semantics
