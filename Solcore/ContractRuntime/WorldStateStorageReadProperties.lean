import Solcore.ContractRuntime.WorldStateStorageRead

/-! Branch laws for conditional WorldState storage reads. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Reading storage from an absent Account remains unavailable. -/
@[simp] theorem WorldState.readStorage?_of_absent
    (state : WorldState)
    (address : Address)
    (slot : Core.Word)
    (absent : state.account? address = none) :
    state.readStorage? address slot = none := by
  simp [WorldState.readStorage?, absent]

/-- Reading from a present Account delegates to its zero-default slot read. -/
@[simp] theorem WorldState.readStorage?_of_present
    (state : WorldState)
    (address : Address)
    (account : Account)
    (slot : Core.Word)
    (present : state.account? address = some account) :
    state.readStorage? address slot = some (account.storageRead slot) := by
  simp [WorldState.readStorage?, present]

end Solcore.ContractRuntime
