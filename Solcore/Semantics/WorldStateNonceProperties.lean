import Solcore.Semantics.AccountNonceProperties
import Solcore.Semantics.WorldStateProperties

/-! Exact nonce lookup and account-preserving update laws. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

@[simp] theorem nonce?_empty (address : Address) :
    WorldState.empty.nonce? address = none := by
  rfl

@[simp] theorem nonce?_putAccount_same
    (state : WorldState)
    (address : Address)
    (account : Account) :
    (state.putAccount address account).nonce? address =
      some account.nonce := by
  simp [WorldState.nonce?, WorldState.account?_putAccount_same]

theorem nonce?_putAccount_other
    (state : WorldState)
    (address other : Address)
    (account : Account)
    (different : other ≠ address) :
    (state.putAccount address account).nonce? other =
      state.nonce? other := by
  simp [WorldState.nonce?,
    WorldState.account?_putAccount_other state address other account different]

theorem writeNonce?_of_absent
    (state : WorldState)
    (address : Address)
    (nonce : Core.Word)
    (absent : state.account? address = none) :
    state.writeNonce? address nonce = none := by
  simp [WorldState.writeNonce?, absent]

theorem writeNonce?_of_present
    (state : WorldState)
    (address : Address)
    (account : Account)
    (nonce : Core.Word)
    (present : state.account? address = some account) :
    state.writeNonce? address nonce =
      some (state.putAccount address (account.withNonce nonce)) := by
  simp [WorldState.writeNonce?, present]

theorem account?_writeNonce?_same
    (state : WorldState)
    (address : Address)
    (account : Account)
    (nonce : Core.Word)
    (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind
        (fun next => next.account? address) =
      some (account.withNonce nonce) := by
  rw [writeNonce?_of_present state address account nonce present]
  simpa using WorldState.account?_putAccount_same state address
    (account.withNonce nonce)

theorem nonce?_writeNonce?_same
    (state : WorldState)
    (address : Address)
    (account : Account)
    (nonce : Core.Word)
    (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind
        (fun next => next.nonce? address) = some nonce := by
  rw [writeNonce?_of_present state address account nonce present]
  simp

theorem account?_writeNonce?_other
    (state : WorldState)
    (address other : Address)
    (account : Account)
    (nonce : Core.Word)
    (present : state.account? address = some account)
    (different : other ≠ address) :
    (state.writeNonce? address nonce).bind
        (fun next => next.account? other) = state.account? other := by
  rw [writeNonce?_of_present state address account nonce present]
  simpa using WorldState.account?_putAccount_other state address other
    (account.withNonce nonce) different

theorem writeNonce?_preserves_payload
    (state : WorldState)
    (address : Address)
    (account : Account)
    (nonce : Core.Word)
    (present : state.account? address = some account) :
    (state.writeNonce? address nonce).bind (fun next =>
        (next.account? address).map fun updated =>
          (updated.code?, updated.balance,
            fun slot => updated.storageValue? slot)) =
      some (account.code?, account.balance,
        fun slot => account.storageValue? slot) := by
  rw [writeNonce?_of_present state address account nonce present]
  simp [WorldState.account?_putAccount_same]

end Solcore.Semantics.WorldState
