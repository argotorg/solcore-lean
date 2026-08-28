import Solcore.Semantics.WorldStateProperties
import Solcore.Semantics.WorldStateUpdateAlgebraProperties

set_option autoImplicit false

namespace Solcore.Semantics

private theorem WorldState.writeStorage?_of_present
    (state : WorldState)
    (address : Address)
    (account : Account)
    (slot value : Core.Word)
    (present : state.account? address = some account) :
    state.writeStorage? address slot value =
      some (state.putAccount address (account.storageWrite slot value)) := by
  simp [WorldState.writeStorage?, present]

@[simp] theorem WorldState.writeStorage?_overwrite
    (state : WorldState)
    (address : Address)
    (slot first second : Core.Word) :
    (state.writeStorage? address slot first).bind
        (fun next => next.writeStorage? address slot second) =
      state.writeStorage? address slot second := by
  cases present : state.account? address with
  | none =>
      rw [WorldState.writeStorage?_of_absent state address slot first present]
      rw [WorldState.writeStorage?_of_absent state address slot second present]
      rfl
  | some account =>
      rw [WorldState.writeStorage?_of_present state address account slot first
        present]
      simp only [Option.bind_some]
      rw [WorldState.writeStorage?_of_present
        (state.putAccount address (account.storageWrite slot first)) address
        (account.storageWrite slot first) slot second
        (WorldState.account?_putAccount_same state address
          (account.storageWrite slot first))]
      rw [WorldState.writeStorage?_of_present state address account slot second
        present]
      simp

theorem WorldState.writeStorage?_commute_slots
    (state : WorldState)
    (address : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (state.writeStorage? address leftSlot leftValue).bind
        (fun next => next.writeStorage? address rightSlot rightValue) =
      (state.writeStorage? address rightSlot rightValue).bind
        (fun next => next.writeStorage? address leftSlot leftValue) := by
  cases present : state.account? address with
  | none =>
      rw [WorldState.writeStorage?_of_absent state address leftSlot leftValue
        present]
      rw [WorldState.writeStorage?_of_absent state address rightSlot rightValue
        present]
      rfl
  | some account =>
      rw [WorldState.writeStorage?_of_present state address account leftSlot
        leftValue present]
      rw [WorldState.writeStorage?_of_present state address account rightSlot
        rightValue present]
      simp only [Option.bind_some]
      rw [WorldState.writeStorage?_of_present
        (state.putAccount address (account.storageWrite leftSlot leftValue))
        address (account.storageWrite leftSlot leftValue) rightSlot rightValue
        (WorldState.account?_putAccount_same state address
          (account.storageWrite leftSlot leftValue))]
      rw [WorldState.writeStorage?_of_present
        (state.putAccount address (account.storageWrite rightSlot rightValue))
        address (account.storageWrite rightSlot rightValue) leftSlot leftValue
        (WorldState.account?_putAccount_same state address
          (account.storageWrite rightSlot rightValue))]
      rw [Account.storageWrite_commute account leftSlot leftValue rightSlot
        rightValue different]
      simp

end Solcore.Semantics
