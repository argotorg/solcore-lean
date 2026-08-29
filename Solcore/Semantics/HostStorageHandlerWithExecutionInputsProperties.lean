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

end Solcore.Semantics.HostStorageDriver
