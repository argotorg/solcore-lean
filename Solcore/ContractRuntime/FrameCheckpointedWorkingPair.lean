import Solcore.ContractRuntime.FrameCheckpointSnapshot
import Solcore.ContractRuntime.WorldState

/-! Structural pairing of one frame checkpoint with independent working values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- One checkpoint snapshot paired with independent state-and-effects working values. -/
structure FrameCheckpointedWorkingPair
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  checkpoint : FrameCheckpointSnapshot RollbackState TraceState
  working : WorldState × FrameEffectJournal RollbackState TraceState

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWrite`
-/

/-! Working-world storage writes for checkpointed frame values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPair

universe u v

/-- Conditionally update storage in only the working world state. -/
def writeWorkingStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot value : Core.Word) :
    Option (FrameCheckpointedWorkingPair RollbackState TraceState) :=
  (values.working.1.writeStorage? address slot value).map fun state =>
    ⟨values.checkpoint, (state, values.working.2)⟩

end Solcore.ContractRuntime.FrameCheckpointedWorkingPair

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWriteProperties`
-/

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

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairStorageWriteAlgebraProperties`
-/

/-! Sequential storage-write algebra lifted to checkpointed working pairs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPair

universe u v

private theorem writeWorkingStorage?_bind_eq_map_bind
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (firstAddress : Address) (firstSlot firstValue : Core.Word)
    (secondAddress : Address) (secondSlot secondValue : Core.Word) :
    (values.writeWorkingStorage? firstAddress firstSlot firstValue).bind
        (fun next =>
          next.writeWorkingStorage? secondAddress secondSlot secondValue) =
      ((values.working.1.writeStorage?
          firstAddress firstSlot firstValue).bind
        (fun state =>
          state.writeStorage? secondAddress secondSlot secondValue)).map
        (fun state =>
          ⟨values.checkpoint, (state, values.working.2)⟩) := by
  simp only [writeWorkingStorage?, Option.bind_map, Option.map_bind]
  rfl

/-- A later write to the same address and slot supersedes an earlier write. -/
theorem writeWorkingStorage?_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address) (slot first second : Core.Word) :
    (values.writeWorkingStorage? address slot first).bind
        (fun next => next.writeWorkingStorage? address slot second) =
      values.writeWorkingStorage? address slot second := by
  rw [writeWorkingStorage?_bind_eq_map_bind]
  simp [writeWorkingStorage?]

/-- Writes to distinct slots at one address commute. -/
theorem writeWorkingStorage?_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (address : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (values.writeWorkingStorage? address leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? address rightSlot rightValue) =
      (values.writeWorkingStorage? address rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? address leftSlot leftValue) := by
  rw [writeWorkingStorage?_bind_eq_map_bind]
  rw [writeWorkingStorage?_bind_eq_map_bind]
  rw [WorldState.writeStorage?_commute_slots
    values.working.1 address leftSlot leftValue rightSlot rightValue different]

/-- Writes to distinct addresses commute. -/
theorem writeWorkingStorage?_commute_addresses
    {RollbackState : Type u} {TraceState : Type v}
    (values : FrameCheckpointedWorkingPair RollbackState TraceState)
    (leftAddress rightAddress : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftAddress ≠ rightAddress) :
    (values.writeWorkingStorage? leftAddress leftSlot leftValue).bind
        (fun next =>
          next.writeWorkingStorage? rightAddress rightSlot rightValue) =
      (values.writeWorkingStorage? rightAddress rightSlot rightValue).bind
        (fun next =>
          next.writeWorkingStorage? leftAddress leftSlot leftValue) := by
  rw [writeWorkingStorage?_bind_eq_map_bind]
  rw [writeWorkingStorage?_bind_eq_map_bind]
  rw [WorldState.writeStorage?_commute_addresses
    values.working.1 leftAddress rightAddress leftSlot leftValue
      rightSlot rightValue different]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPair
