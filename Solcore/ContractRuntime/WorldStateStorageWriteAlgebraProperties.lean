import Solcore.ContractRuntime.WorldStateProperties
import Solcore.ContractRuntime.WorldStateUpdateAlgebraProperties

set_option autoImplicit false

namespace Solcore.ContractRuntime

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

theorem WorldState.writeStorage?_commute_addresses
    (state : WorldState)
    (leftAddress rightAddress : Address)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftAddress ≠ rightAddress) :
    (state.writeStorage? leftAddress leftSlot leftValue).bind
        (fun next =>
          next.writeStorage? rightAddress rightSlot rightValue) =
      (state.writeStorage? rightAddress rightSlot rightValue).bind
        (fun next =>
          next.writeStorage? leftAddress leftSlot leftValue) := by
  have reverse : rightAddress ≠ leftAddress := Ne.symm different
  cases leftPresent : state.account? leftAddress with
  | none =>
      rw [WorldState.writeStorage?_of_absent state leftAddress leftSlot
        leftValue leftPresent]
      simp only [Option.bind_none]
      cases rightPresent : state.account? rightAddress with
      | none =>
          rw [WorldState.writeStorage?_of_absent state rightAddress rightSlot
            rightValue rightPresent]
          rfl
      | some rightAccount =>
          rw [WorldState.writeStorage?_of_present state rightAddress
            rightAccount rightSlot rightValue rightPresent]
          simp only [Option.bind_some]
          have leftAfter :
              (state.putAccount rightAddress
                (rightAccount.storageWrite rightSlot rightValue)).account?
                  leftAddress = none := by
            rw [WorldState.account?_putAccount_other state rightAddress
              leftAddress (rightAccount.storageWrite rightSlot rightValue)
              different]
            exact leftPresent
          rw [WorldState.writeStorage?_of_absent
            (state.putAccount rightAddress
              (rightAccount.storageWrite rightSlot rightValue))
            leftAddress leftSlot leftValue leftAfter]
  | some leftAccount =>
      cases rightPresent : state.account? rightAddress with
      | none =>
          rw [WorldState.writeStorage?_of_present state leftAddress leftAccount
            leftSlot leftValue leftPresent]
          simp only [Option.bind_some]
          have rightAfter :
              (state.putAccount leftAddress
                (leftAccount.storageWrite leftSlot leftValue)).account?
                  rightAddress = none := by
            rw [WorldState.account?_putAccount_other state leftAddress
              rightAddress (leftAccount.storageWrite leftSlot leftValue)
              reverse]
            exact rightPresent
          rw [WorldState.writeStorage?_of_absent
            (state.putAccount leftAddress
              (leftAccount.storageWrite leftSlot leftValue))
            rightAddress rightSlot rightValue rightAfter]
          rw [WorldState.writeStorage?_of_absent state rightAddress rightSlot
            rightValue rightPresent]
          rfl
      | some rightAccount =>
          rw [WorldState.writeStorage?_of_present state leftAddress leftAccount
            leftSlot leftValue leftPresent]
          rw [WorldState.writeStorage?_of_present state rightAddress
            rightAccount rightSlot rightValue rightPresent]
          simp only [Option.bind_some]
          have rightAfter :
              (state.putAccount leftAddress
                (leftAccount.storageWrite leftSlot leftValue)).account?
                  rightAddress = some rightAccount := by
            rw [WorldState.account?_putAccount_other state leftAddress
              rightAddress (leftAccount.storageWrite leftSlot leftValue)
              reverse]
            exact rightPresent
          have leftAfter :
              (state.putAccount rightAddress
                (rightAccount.storageWrite rightSlot rightValue)).account?
                  leftAddress = some leftAccount := by
            rw [WorldState.account?_putAccount_other state rightAddress
              leftAddress (rightAccount.storageWrite rightSlot rightValue)
              different]
            exact leftPresent
          rw [WorldState.writeStorage?_of_present
            (state.putAccount leftAddress
              (leftAccount.storageWrite leftSlot leftValue))
            rightAddress rightAccount rightSlot rightValue rightAfter]
          rw [WorldState.writeStorage?_of_present
            (state.putAccount rightAddress
              (rightAccount.storageWrite rightSlot rightValue))
            leftAddress leftAccount leftSlot leftValue leftAfter]
          exact congrArg some (WorldState.putAccount_commute state leftAddress
            rightAddress (leftAccount.storageWrite leftSlot leftValue)
            (rightAccount.storageWrite rightSlot rightValue) different)

theorem WorldState.writeStorage?_zero_deletes
    (state : WorldState) (address : Address)
    (account : Account) (slot : Core.Word)
    (present : state.account? address = some account) :
    ∃ next,
      state.writeStorage? address slot Core.Word.zero = some next ∧
      next.account? address =
        some (account.storageWrite slot Core.Word.zero) ∧
      (account.storageWrite slot Core.Word.zero).storageValue? slot = none := by
  refine ⟨state.putAccount address
      (account.storageWrite slot Core.Word.zero), ?_, ?_, ?_⟩
  · exact WorldState.writeStorage?_of_present state address account slot
      Core.Word.zero present
  · exact WorldState.account?_putAccount_same state address
      (account.storageWrite slot Core.Word.zero)
  · exact Account.storageValue?_storageWrite_zero account slot

end Solcore.ContractRuntime
