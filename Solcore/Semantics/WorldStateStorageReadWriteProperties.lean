import Solcore.Semantics.WorldStateStorageReadProperties
import Solcore.Semantics.WorldStateProperties

/-! Stage-preserving observations of conditional WorldState storage writes. -/

set_option autoImplicit false

namespace Solcore.Semantics

set_option doc.verso true in
/-- Reading the written slot observes the new value after a successful world
storage write. Account presence is retained in the optional result: a missing
account does not become an account with a zero-valued slot.
-/
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

set_option doc.verso true in
/-- Writing a different slot preserves the selected slot's read, provided the
addressed account exists. The inequality premise identifies the read that is
unaffected; account absence remains explicit in the optional result.
-/
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

set_option doc.verso true in
/-- Writing a different address preserves the selected address and slot's read.
The inequality premise separates the accounts, and the optional result retains
the requirement that the written account exists.
-/
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
