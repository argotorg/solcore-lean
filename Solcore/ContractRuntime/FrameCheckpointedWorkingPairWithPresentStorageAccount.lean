import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-! Evidence that an address-bound working context contains its selected Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- An address-bound working context paired with its present selected Account. -/
structure FrameCheckpointedWorkingPairWithPresentStorageAccount
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  context :
    FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState
  storageAccount : Account
  storageAccount_present :
    context.values.working.1.account? context.storageAddress =
      some storageAccount

namespace FrameCheckpointedWorkingPairWithStorageAddress

/-- Refine a context exactly when its selected working Account is present. -/
def withPresentStorageAccount?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState) :
    Option
      (FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState) :=
  match present :
      context.values.working.1.account? context.storageAddress with
  | none => none
  | some account => some ⟨context, account, present⟩

end FrameCheckpointedWorkingPairWithStorageAddress

end Solcore.ContractRuntime
