import Solcore.Semantics.FrameCheckpointedWorkingPairStorageWrite
import Solcore.Semantics.WorldStateStorageWriteAlgebraProperties

/-! Sequential storage-write algebra lifted to checkpointed working pairs. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPair

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

end Solcore.Semantics.FrameCheckpointedWorkingPair
