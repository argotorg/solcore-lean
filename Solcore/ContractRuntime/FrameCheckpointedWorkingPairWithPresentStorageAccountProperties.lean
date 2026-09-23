import Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithPresentStorageAccount

/-! Branch laws for refining an address-bound context by working Account presence. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- A missing selected working Account makes refinement unavailable. -/
@[simp] theorem withPresentStorageAccount?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.withPresentStorageAccount? = none := by
  unfold withPresentStorageAccount?
  split <;> simp_all

/-- A present selected working Account produces its exact evidence carrier. -/
@[simp] theorem withPresentStorageAccount?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.withPresentStorageAccount? =
      some ⟨context, account, present⟩ := by
  unfold withPresentStorageAccount?
  split
  · simp_all
  · rename_i account' observed
    have same : account' = account :=
      Option.some.inj (observed.symm.trans present)
    subst account'
    rfl

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
