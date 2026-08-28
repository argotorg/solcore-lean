import Solcore.Core.HostMachine
import Solcore.Semantics.FrameCheckpointedWorkingPairWithPresentStorageAccountStorageRead

/-! Interpretation of one Core storage-read request by a proven-present Account. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u v

/--
Read from the selected working Account and resume Core without changing the
proven-present runtime context.
-/
def handleStorageReadSuspension
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState × Core.State :=
  match suspension.request with
  | .storageRead slot =>
      (context, suspension.resume (context.readStorage slot))

@[simp] theorem handleStorageReadSuspension_context
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleStorageReadSuspension context suspension).1 = context := by
  cases suspension with
  | mk request continuation store =>
      cases request
      rfl

@[simp] theorem handleStorageReadSuspension_storageRead
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleStorageReadSuspension context
        ⟨.storageRead slot, continuation, store⟩ =
      (context,
        ⟨.ret (.word (context.readStorage slot)), continuation, store⟩) :=
  rfl

@[simp] theorem handleStorageReadSuspension_continuation
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleStorageReadSuspension context suspension).2.continuation =
      suspension.continuation := by
  cases suspension with
  | mk request continuation store =>
      cases request
      rfl

@[simp] theorem handleStorageReadSuspension_store
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleStorageReadSuspension context suspension).2.store = suspension.store := by
  cases suspension with
  | mk request continuation store =>
      cases request
      rfl

end Solcore.Semantics
