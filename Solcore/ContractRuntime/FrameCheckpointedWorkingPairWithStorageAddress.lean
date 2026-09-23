import Solcore.ContractRuntime.FrameCheckpointedWorkingPair
import Solcore.ContractRuntime.WorldStateStorageRead

/-! A caller-addressed storage boundary over checkpointed working values. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

/-- A checkpointed working pair with one caller-supplied storage address. -/
structure FrameCheckpointedWorkingPairWithStorageAddress
    (RollbackState : Type u) (TraceState : Type v) : Type (max u v) where
  storageAddress : Address
  values : FrameCheckpointedWorkingPair RollbackState TraceState

namespace FrameCheckpointedWorkingPairWithStorageAddress

/-- Write one slot at the stored address in only the working world state. -/
def writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    Option
      (FrameCheckpointedWorkingPairWithStorageAddress
        RollbackState TraceState) :=
  (context.values.writeWorkingStorage?
    context.storageAddress slot value).map fun values =>
      ⟨context.storageAddress, values⟩

end FrameCheckpointedWorkingPairWithStorageAddress

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressProperties`
-/

/-! Branch laws for address-bound checkpointed working storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- An absent working account makes the address-bound write unavailable. -/
@[simp] theorem writeStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.writeStorage? slot value = none := by
  simp [writeStorage?,
    FrameCheckpointedWorkingPair.writeWorkingStorage?_of_absent,
    absent]

/-- A present working account updates only the addressed working storage. -/
@[simp] theorem writeStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account) (slot value : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.writeStorage? slot value =
      some
        ⟨context.storageAddress,
          ⟨context.values.checkpoint,
            (context.values.working.1.putAccount context.storageAddress
              (account.storageWrite slot value),
              context.values.working.2)⟩⟩ := by
  simp [writeStorage?,
    FrameCheckpointedWorkingPair.writeWorkingStorage?_of_present,
    present]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageRead`
-/

/-! Working-storage reads through a retained frame storage address. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Read one slot from the stored address in the working WorldState. -/
def readStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot : Core.Word) : Option Core.Word :=
  context.values.working.1.readStorage? context.storageAddress slot

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageReadProperties`
-/

/-! Branch laws for address-bound working storage reads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- An absent addressed working Account makes the read unavailable. -/
@[simp] theorem readStorage?_of_absent
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot : Core.Word)
    (absent :
      context.values.working.1.account? context.storageAddress = none) :
    context.readStorage? slot = none := by
  exact WorldState.readStorage?_of_absent context.values.working.1
    context.storageAddress slot absent

/-- A present addressed working Account supplies its zero-default slot read. -/
@[simp] theorem readStorage?_of_present
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (account : Account)
    (slot : Core.Word)
    (present :
      context.values.working.1.account? context.storageAddress = some account) :
    context.readStorage? slot = some (account.storageRead slot) := by
  exact WorldState.readStorage?_of_present context.values.working.1
    context.storageAddress account slot present

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageReadWriteProperties`
-/

/-! Read-after-write laws for address-bound working storage. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Reading the written slot observes the new value after a successful write. -/
@[simp] theorem readStorage?_writeStorage?_same
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.readStorage? slot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => some value) := by
  simp [writeStorage?, FrameCheckpointedWorkingPair.writeWorkingStorage?,
    readStorage?, Function.comp_def]

/-- Writing another slot preserves the selected working-storage read. -/
@[simp] theorem readStorage?_writeStorage?_other_slot
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (context.writeStorage? writtenSlot value).map
        (fun next => next.readStorage? readSlot) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.readStorage? readSlot) := by
  simp [writeStorage?, FrameCheckpointedWorkingPair.writeWorkingStorage?,
    readStorage?, Function.comp_def, different]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageWriteAlgebraProperties`
-/

/-! Sequential storage-write algebra through one retained storage address. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

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

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageWriteCoherenceProperties`
-/

/-! Values coherence for retained-address and address-parameterized writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- Forgetting the retained selector recovers the underlying values write. -/
@[simp] theorem values_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map (fun next => next.values) =
      context.values.writeWorkingStorage?
        context.storageAddress slot value := by
  cases result : context.values.writeWorkingStorage?
      context.storageAddress slot value <;>
    simp [writeStorage?, result]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddressStorageWritePreservationProperties`
-/

/-! Stage-preserving structural observations of address-bound storage writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress

universe u v

/-- A conditional write retains the exact stored address in its success branch. -/
@[simp] theorem storageAddress_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.storageAddress) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.storageAddress) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

/-- A conditional write retains the exact checkpoint in its success branch. -/
@[simp] theorem checkpoint_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.values.checkpoint) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.values.checkpoint) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

/-- A conditional write retains the exact working effects in its success branch. -/
@[simp] theorem workingEffects_writeStorage?
    {RollbackState : Type u} {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithStorageAddress RollbackState TraceState)
    (slot value : Core.Word) :
    (context.writeStorage? slot value).map
        (fun next => next.values.working.2) =
      (context.values.working.1.account? context.storageAddress).map
        (fun _ => context.values.working.2) := by
  cases present :
      context.values.working.1.account? context.storageAddress <;>
    simp [present]

end Solcore.ContractRuntime.FrameCheckpointedWorkingPairWithStorageAddress
