import Solcore.ContractRuntime.Account
import Solcore.ContractRuntime.WorldState

/-! Exact balance lookup and account-preserving update laws. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

@[simp] theorem balance?_empty (address : Address) :
    WorldState.empty.balance? address = none := by
  rfl

@[simp] theorem balance?_putAccount_same
    (state : WorldState)
    (address : Address)
    (account : Account) :
    (state.putAccount address account).balance? address =
      some account.balance := by
  simp [WorldState.balance?, WorldState.account?_putAccount_same]

theorem balance?_putAccount_other
    (state : WorldState)
    (address other : Address)
    (account : Account)
    (different : other ≠ address) :
    (state.putAccount address account).balance? other =
      state.balance? other := by
  simp [WorldState.balance?,
    WorldState.account?_putAccount_other state address other account different]

theorem writeBalance?_of_absent
    (state : WorldState)
    (address : Address)
    (balance : Core.Word)
    (absent : state.account? address = none) :
    state.writeBalance? address balance = none := by
  simp [WorldState.writeBalance?, absent]

theorem writeBalance?_of_present
    (state : WorldState)
    (address : Address)
    (account : Account)
    (balance : Core.Word)
    (present : state.account? address = some account) :
    state.writeBalance? address balance =
      some (state.putAccount address (account.withBalance balance)) := by
  simp [WorldState.writeBalance?, present]

theorem balance?_writeBalance?_same
    (state : WorldState)
    (address : Address)
    (account : Account)
    (balance : Core.Word)
    (present : state.account? address = some account) :
    (state.writeBalance? address balance).bind
        (fun next => next.balance? address) = some balance := by
  rw [writeBalance?_of_present state address account balance present]
  simp

theorem account?_writeBalance?_other
    (state : WorldState)
    (address other : Address)
    (account : Account)
    (balance : Core.Word)
    (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeBalance? address balance).bind
        (fun next => next.account? other) = state.account? other := by
  rw [writeBalance?_of_present state address account balance present]
  simpa using WorldState.account?_putAccount_other state address other
    (account.withBalance balance) different

end Solcore.ContractRuntime.WorldState
