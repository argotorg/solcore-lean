import Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWrite

/-! Branch laws for checkpointed working-world storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPair

universe u v

/-- A missing working account makes the lifted write unavailable. -/
@[simp] theorem writeWorkingStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot value : Core.Word)
    (absent : values.working.1.account? address = none) :
    values.writeWorkingStorage? address slot value = none := by
  simp [writeWorkingStorage?, WorldState.writeStorage?, absent]

/-- A present working account changes only the working world state. -/
@[simp] theorem writeWorkingStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (account : Account)
    (slot value : Core.Word)
    (present : values.working.1.account? address = some account) :
    values.writeWorkingStorage? address slot value =
      some ⟨values.checkpoint,
        (values.working.1.putAccount address
          (account.storageWrite slot value), values.working.2)⟩ := by
  simp [writeWorkingStorage?, WorldState.writeStorage?, present]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPair
