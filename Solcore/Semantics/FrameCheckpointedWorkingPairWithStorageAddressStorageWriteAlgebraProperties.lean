import Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
import Solcore.Semantics.FrameCheckpointedWorkingPairStorageWriteAlgebraProperties

/-! Sequential storage-write algebra through one retained storage address. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

private theorem writeStorage?_bind_eq_map_bind
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (firstSlot firstValue secondSlot secondValue : Core.Word) :
    (context.writeStorage? firstSlot firstValue).bind
        (fun next => next.writeStorage? secondSlot secondValue) =
      ((context.values.writeWorkingStorage?
          context.storageAddress firstSlot firstValue).bind
        (fun values =>
          values.writeWorkingStorage?
            context.storageAddress secondSlot secondValue)).map
        (fun values => ⟨context.storageAddress, values⟩) := by
  simp only [writeStorage?, Option.bind_map, Option.map_bind]
  rfl

/-- A later write to the retained address and slot supersedes an earlier one. -/
theorem writeStorage?_overwrite
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot first second : Core.Word) :
    (context.writeStorage? slot first).bind
        (fun next => next.writeStorage? slot second) =
      context.writeStorage? slot second := by
  rw [writeStorage?_bind_eq_map_bind]
  unfold writeStorage?
  rw [FrameCheckpointedWorkingPair.writeWorkingStorage?_overwrite]

/-- Writes to distinct slots at the retained address commute. -/
theorem writeStorage?_commute_slots
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (context.writeStorage? leftSlot leftValue).bind
        (fun next => next.writeStorage? rightSlot rightValue) =
      (context.writeStorage? rightSlot rightValue).bind
        (fun next => next.writeStorage? leftSlot leftValue) := by
  rw [writeStorage?_bind_eq_map_bind]
  rw [writeStorage?_bind_eq_map_bind]
  rw [FrameCheckpointedWorkingPair.writeWorkingStorage?_commute_slots
    context.values context.storageAddress leftSlot leftValue
      rightSlot rightValue different]

end Solcore.Semantics.FrameCheckpointedWorkingPairWithStorageAddress
