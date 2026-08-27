import Solcore.Semantics.WorldState
import Std.Data.ExtTreeMap.Lemmas

set_option autoImplicit false

namespace Solcore.Semantics

theorem WorldState.account?_empty (address : Address) :
    WorldState.empty.account? address = none := by
  simp [WorldState.empty, WorldState.account?]

theorem WorldState.account?_putAccount_same
    (state : WorldState)
    (address : Address)
    (account : Account) :
    (state.putAccount address account).account? address = some account := by
  simp [WorldState.putAccount, WorldState.account?]

theorem WorldState.account?_putAccount_other
    (state : WorldState)
    (address other : Address)
    (account : Account)
    (different : other ≠ address) :
    (state.putAccount address account).account? other =
      state.account? other := by
  have address_ne_other : address ≠ other :=
    fun equal => different equal.symm
  simp [WorldState.putAccount, WorldState.account?,
    Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert,
    address_ne_other]

theorem Account.storageValue?_empty (slot : Core.Word) :
    Account.empty.storageValue? slot = none := by
  simp [Account.empty, Account.storageValue?]

theorem Account.storageRead_empty (slot : Core.Word) :
    Account.empty.storageRead slot = Core.Word.zero := by
  simp [Account.empty, Account.storageRead, Account.storageValue?]

theorem Account.storageRead_storageWrite_same
    (account : Account)
    (slot value : Core.Word) :
    (account.storageWrite slot value).storageRead slot = value := by
  by_cases zero : value = Core.Word.zero
  · simp [Account.storageWrite, Account.storageRead,
      Account.storageValue?, zero]
  · simp [Account.storageWrite, Account.storageRead,
      Account.storageValue?, zero]

theorem Account.storageValue?_storageWrite_zero
    (account : Account)
    (slot : Core.Word) :
    (account.storageWrite slot Core.Word.zero).storageValue? slot = none := by
  simp [Account.storageWrite, Account.storageValue?]

theorem Account.storageValue?_storageWrite_nonzero
    (account : Account)
    (slot value : Core.Word)
    (nonzero : value ≠ Core.Word.zero) :
    (account.storageWrite slot value).storageValue? slot = some value := by
  simp [Account.storageWrite, Account.storageValue?, nonzero]

theorem Account.storageRead_storageWrite_other
    (account : Account)
    (slot value other : Core.Word)
    (different : other ≠ slot) :
    (account.storageWrite slot value).storageRead other =
      account.storageRead other := by
  have slot_ne_other : slot ≠ other :=
    fun equal => different equal.symm
  by_cases zero : value = Core.Word.zero
  · simp [Account.storageWrite, Account.storageRead,
      Account.storageValue?, zero, Std.ExtTreeMap.get?_eq_getElem?,
      Std.ExtTreeMap.getElem?_erase, slot_ne_other]
  · simp [Account.storageWrite, Account.storageRead,
      Account.storageValue?, zero, Std.ExtTreeMap.get?_eq_getElem?,
      Std.ExtTreeMap.getElem?_insert, slot_ne_other]

theorem WorldState.writeStorage?_of_absent
    (state : WorldState)
    (address : Address)
    (slot value : Core.Word)
    (absent : state.account? address = none) :
    state.writeStorage? address slot value = none := by
  simp [WorldState.writeStorage?, absent]

theorem WorldState.account?_writeStorage?_same
    (state : WorldState)
    (address : Address)
    (account : Account)
    (slot value : Core.Word)
    (present : state.account? address = some account) :
    (state.writeStorage? address slot value).bind
        (fun next => next.account? address) =
      some (account.storageWrite slot value) := by
  rw [show state.writeStorage? address slot value =
      some (state.putAccount address (account.storageWrite slot value)) by
    simp [WorldState.writeStorage?, present]]
  simp [WorldState.account?_putAccount_same]

theorem WorldState.account?_writeStorage?_other
    (state : WorldState)
    (address other : Address)
    (account : Account)
    (slot value : Core.Word)
    (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeStorage? address slot value).bind
        (fun next => next.account? other) =
      state.account? other := by
  rw [show state.writeStorage? address slot value =
      some (state.putAccount address (account.storageWrite slot value)) by
    simp [WorldState.writeStorage?, present]]
  simpa using WorldState.account?_putAccount_other state address other
    (account.storageWrite slot value) different

end Solcore.Semantics
