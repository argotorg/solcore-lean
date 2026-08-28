import Solcore.Semantics.WorldStateStorageReadProperties
import Solcore.Semantics.WorldStateProperties

/-! Stage-preserving observations of conditional WorldState storage writes. -/

set_option autoImplicit false

namespace Solcore.Semantics

/-- Reading the written slot observes the new value after a successful write. -/
@[simp] theorem WorldState.readStorage?_writeStorage?_same
    (state : WorldState) (address : Address)
    (slot value : Core.Word) :
    (state.writeStorage? address slot value).map
        (fun next => next.readStorage? address slot) =
      (state.account? address).map (fun _ => some value) := by
  cases present : state.account? address with
  | none =>
      rw [WorldState.writeStorage?_of_absent state address slot value present]
      simp
  | some account =>
      have written :
          state.writeStorage? address slot value =
            some (state.putAccount address
              (account.storageWrite slot value)) := by
        simp [WorldState.writeStorage?, present]
      rw [written]
      simp only [Option.map_some]
      rw [WorldState.readStorage?_of_present
        (state.putAccount address (account.storageWrite slot value))
        address (account.storageWrite slot value) slot
        (WorldState.account?_putAccount_same state address
          (account.storageWrite slot value))]
      rw [Account.storageRead_storageWrite_same]

/-- Writing another slot preserves the selected slot read. -/
@[simp] theorem WorldState.readStorage?_writeStorage?_other_slot
    (state : WorldState) (address : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readSlot ≠ writtenSlot) :
    (state.writeStorage? address writtenSlot value).map
        (fun next => next.readStorage? address readSlot) =
      (state.account? address).map
        (fun _ => state.readStorage? address readSlot) := by
  cases present : state.account? address with
  | none =>
      rw [WorldState.writeStorage?_of_absent state address writtenSlot value
        present]
      simp
  | some account =>
      have written :
          state.writeStorage? address writtenSlot value =
            some (state.putAccount address
              (account.storageWrite writtenSlot value)) := by
        simp [WorldState.writeStorage?, present]
      rw [written]
      simp only [Option.map_some]
      rw [WorldState.readStorage?_of_present
        (state.putAccount address (account.storageWrite writtenSlot value))
        address (account.storageWrite writtenSlot value) readSlot
        (WorldState.account?_putAccount_same state address
          (account.storageWrite writtenSlot value))]
      rw [Account.storageRead_storageWrite_other account writtenSlot value
        readSlot different]
      simp [present]

/-- Writing another address preserves the selected address read. -/
@[simp] theorem WorldState.readStorage?_writeStorage?_other_address
    (state : WorldState) (writtenAddress readAddress : Address)
    (writtenSlot value readSlot : Core.Word)
    (different : readAddress ≠ writtenAddress) :
    (state.writeStorage? writtenAddress writtenSlot value).map
        (fun next => next.readStorage? readAddress readSlot) =
      (state.account? writtenAddress).map
        (fun _ => state.readStorage? readAddress readSlot) := by
  cases present : state.account? writtenAddress with
  | none =>
      rw [WorldState.writeStorage?_of_absent state writtenAddress writtenSlot
        value present]
      simp
  | some account =>
      have written :
          state.writeStorage? writtenAddress writtenSlot value =
            some (state.putAccount writtenAddress
              (account.storageWrite writtenSlot value)) := by
        simp [WorldState.writeStorage?, present]
      have readPreserved :
          (state.putAccount writtenAddress
            (account.storageWrite writtenSlot value)).readStorage?
              readAddress readSlot =
            state.readStorage? readAddress readSlot := by
        simp only [WorldState.readStorage?]
        rw [WorldState.account?_putAccount_other state writtenAddress
          readAddress (account.storageWrite writtenSlot value) different]
      rw [written]
      simp only [Option.map_some]
      rw [readPreserved]

end Solcore.Semantics
