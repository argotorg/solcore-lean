import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.WorldState

/-!
# Laws of balances, nonces and deltas

Balance and nonce lookup under account updates, and the endpoint queries of `WorldStateDelta`. These
stay apart from `WorldStateLaws` because many modules reach that file and not this one.
-/

section
-- leanmerge: from Solcore.ContractRuntime.WorldStateBalanceProperties
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
end

section
-- leanmerge: from Solcore.ContractRuntime.WorldStateNonceProperties
/-! Exact nonce lookup and account-preserving update laws. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

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

end Solcore.ContractRuntime.WorldState
end

section
-- leanmerge: from Solcore.ContractRuntime.WorldStateDelta
/-! Exact, queryable endpoint observations for arbitrary WorldState transitions. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateDeltaProperties`
-/

/-! Endpoint laws for exact, queryable WorldState transitions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldStateDelta

/-- The indexed endpoint worlds determine exactly one WorldStateDelta value. -/
theorem unique
    {initialWorld finalWorld : WorldState}
    (left right : WorldStateDelta initialWorld finalWorld) :
    left = right := by
  cases left
  cases right
  rfl

@[simp] theorem accountEndpoints_exact
    (initialWorld finalWorld : WorldState)
    (address : Address) :
    (WorldStateDelta.exact (initialWorld := initialWorld)
      (finalWorld := finalWorld)).accountEndpoints address =
      (initialWorld.account? address, finalWorld.account? address) := by
  rfl

@[simp] theorem storageEndpoints_exact
    (initialWorld finalWorld : WorldState)
    (address : Address)
    (slot : Core.Word) :
    (WorldStateDelta.exact (initialWorld := initialWorld)
      (finalWorld := finalWorld)).storageEndpoints address slot =
      (initialWorld.readStorage? address slot,
        finalWorld.readStorage? address slot) := by
  rfl

@[simp] theorem balanceEndpoints_exact
    (initialWorld finalWorld : WorldState)
    (address : Address) :
    (WorldStateDelta.exact (initialWorld := initialWorld)
      (finalWorld := finalWorld)).balanceEndpoints address =
      (initialWorld.balance? address, finalWorld.balance? address) := by
  rfl

@[simp] theorem nonceEndpoints_exact
    (initialWorld finalWorld : WorldState)
    (address : Address) :
    (WorldStateDelta.exact (initialWorld := initialWorld)
      (finalWorld := finalWorld)).nonceEndpoints address =
      (initialWorld.nonce? address, finalWorld.nonce? address) := by
  rfl

@[simp] theorem codeEndpoints_exact
    (initialWorld finalWorld : WorldState)
    (address : Address) :
    (WorldStateDelta.exact (initialWorld := initialWorld)
      (finalWorld := finalWorld)).codeEndpoints address =
      (initialWorld.code? address, finalWorld.code? address) := by
  rfl

@[simp] theorem createdAccount?_exact
    (initialWorld finalWorld : WorldState)
    (address : Address) :
    (WorldStateDelta.exact (initialWorld := initialWorld)
      (finalWorld := finalWorld)).createdAccount? address =
      match initialWorld.account? address, finalWorld.account? address with
      | none, some _ => true
      | _, _ => false := by
  rfl

@[simp] theorem accountEndpoints_identity
    (world : WorldState)
    (address : Address) :
    (identity world).accountEndpoints address =
      (world.account? address, world.account? address) := by
  rfl

@[simp] theorem storageEndpoints_identity
    (world : WorldState)
    (address : Address)
    (slot : Core.Word) :
    (identity world).storageEndpoints address slot =
      (world.readStorage? address slot, world.readStorage? address slot) := by
  rfl

@[simp] theorem balanceEndpoints_identity
    (world : WorldState)
    (address : Address) :
    (identity world).balanceEndpoints address =
      (world.balance? address, world.balance? address) := by
  rfl

@[simp] theorem nonceEndpoints_identity
    (world : WorldState)
    (address : Address) :
    (identity world).nonceEndpoints address =
      (world.nonce? address, world.nonce? address) := by
  rfl

@[simp] theorem codeEndpoints_identity
    (world : WorldState)
    (address : Address) :
    (identity world).codeEndpoints address =
      (world.code? address, world.code? address) := by
  rfl

@[simp] theorem createdAccount?_identity
    (world : WorldState)
    (address : Address) :
    (identity world).createdAccount? address = false := by
  unfold createdAccount?
  cases present : world.account? address <;> rfl

@[simp] theorem slotChange?_identity
    (world : WorldState)
    (address : Address)
    (slot : Core.Word) :
    (identity world).slotChange? address slot = none := by
  simp [slotChange?, storageEndpoints]

@[simp] theorem balanceChange?_identity
    (world : WorldState)
    (address : Address) :
    (identity world).balanceChange? address = none := by
  simp [balanceChange?, balanceEndpoints]

@[simp] theorem nonceChange?_identity
    (world : WorldState)
    (address : Address) :
    (identity world).nonceChange? address = none := by
  simp [nonceChange?, nonceEndpoints]

theorem slotChange?_eq_none_iff
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (slot : Core.Word) :
    delta.slotChange? address slot = none ↔
      (delta.storageEndpoints address slot).1 =
        (delta.storageEndpoints address slot).2 := by
  simp [slotChange?]

theorem slotChange?_eq_some_iff
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (slot : Core.Word)
    (before after : Option Core.Word) :
    delta.slotChange? address slot = some (before, after) ↔
      (delta.storageEndpoints address slot).1 = before ∧
      (delta.storageEndpoints address slot).2 = after ∧
      before ≠ after := by
  unfold slotChange?
  by_cases same :
      (delta.storageEndpoints address slot).1 =
        (delta.storageEndpoints address slot).2
  · simp [same]
    intro beforeEq afterEq
    exact beforeEq.symm.trans afterEq
  · simp only [if_neg same, Option.some.injEq]
    constructor
    · intro endpointsEq
      have beforeEq :
          (delta.storageEndpoints address slot).1 = before :=
        congrArg Prod.fst endpointsEq
      have afterEq :
          (delta.storageEndpoints address slot).2 = after :=
        congrArg Prod.snd endpointsEq
      refine ⟨beforeEq, afterEq, ?_⟩
      intro valuesEqual
      apply same
      exact beforeEq.trans (valuesEqual.trans afterEq.symm)
    · rintro ⟨beforeEq, afterEq, _different⟩
      apply Prod.ext
      · exact beforeEq
      · exact afterEq

theorem balanceChange?_eq_none_iff
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) :
    delta.balanceChange? address = none ↔
      (delta.balanceEndpoints address).1 =
        (delta.balanceEndpoints address).2 := by
  simp [balanceChange?]

theorem balanceChange?_eq_some_iff
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (before after : Option Core.Word) :
    delta.balanceChange? address = some (before, after) ↔
      (delta.balanceEndpoints address).1 = before ∧
      (delta.balanceEndpoints address).2 = after ∧
      before ≠ after := by
  unfold balanceChange?
  by_cases same :
      (delta.balanceEndpoints address).1 =
        (delta.balanceEndpoints address).2
  · simp [same]
    intro beforeEq afterEq
    exact beforeEq.symm.trans afterEq
  · simp only [if_neg same, Option.some.injEq]
    constructor
    · intro endpointsEq
      have beforeEq :
          (delta.balanceEndpoints address).1 = before :=
        congrArg Prod.fst endpointsEq
      have afterEq :
          (delta.balanceEndpoints address).2 = after :=
        congrArg Prod.snd endpointsEq
      refine ⟨beforeEq, afterEq, ?_⟩
      intro valuesEqual
      apply same
      exact beforeEq.trans (valuesEqual.trans afterEq.symm)
    · rintro ⟨beforeEq, afterEq, _different⟩
      apply Prod.ext
      · exact beforeEq
      · exact afterEq

theorem nonceChange?_eq_none_iff
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) :
    delta.nonceChange? address = none ↔
      (delta.nonceEndpoints address).1 =
        (delta.nonceEndpoints address).2 := by
  simp [nonceChange?]

theorem nonceChange?_eq_some_iff
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (before after : Option Core.Word) :
    delta.nonceChange? address = some (before, after) ↔
      (delta.nonceEndpoints address).1 = before ∧
      (delta.nonceEndpoints address).2 = after ∧
      before ≠ after := by
  unfold nonceChange?
  by_cases same :
      (delta.nonceEndpoints address).1 =
        (delta.nonceEndpoints address).2
  · simp [same]
    intro beforeEq afterEq
    exact beforeEq.symm.trans afterEq
  · simp only [if_neg same, Option.some.injEq]
    constructor
    · intro endpointsEq
      have beforeEq :
          (delta.nonceEndpoints address).1 = before :=
        congrArg Prod.fst endpointsEq
      have afterEq :
          (delta.nonceEndpoints address).2 = after :=
        congrArg Prod.snd endpointsEq
      refine ⟨beforeEq, afterEq, ?_⟩
      intro valuesEqual
      apply same
      exact beforeEq.trans (valuesEqual.trans afterEq.symm)
    · rintro ⟨beforeEq, afterEq, _different⟩
      apply Prod.ext
      · exact beforeEq
      · exact afterEq

end Solcore.ContractRuntime.WorldStateDelta
end
