import Solcore.ContractRuntime.WorldStateStorageRead
import Solcore.ContractRuntime.WorldStateBalanceProperties
import Solcore.ContractRuntime.WorldStateNonceProperties
import Solcore.ContractRuntime.WorldStateCode

/-! Exact, queryable endpoint observations for arbitrary WorldState transitions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/--
An exact observation of one transition between two WorldState endpoints.

WorldState is function-valued, so this carrier deliberately exposes pointwise
queries instead of claiming that changed accounts or slots can be enumerated.
-/
inductive WorldStateDelta (initialWorld finalWorld : WorldState) : Type where
  /-- The canonical exact observation for the indexed endpoint worlds. -/
  | exact : WorldStateDelta initialWorld finalWorld

namespace WorldStateDelta

/-- The unchanged transition, represented by the same canonical observation. -/
def identity (world : WorldState) : WorldStateDelta world world :=
  .exact

/-- Observe exact account presence and contents at one address. -/
def accountEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option Account × Option Account :=
  (initialWorld.account? address, finalWorld.account? address)

/--
Observe exact storage reads at one address and slot.

Each endpoint remains optional: `none` means that the account is absent, while
`some Core.Word.zero` means that the account is present and the slot reads zero.
-/
def storageEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (slot : Core.Word) : Option Core.Word × Option Core.Word :=
  (initialWorld.readStorage? address slot,
    finalWorld.readStorage? address slot)

/--
Observe exact balance endpoints at one address.

`none` denotes an absent account and `some Core.Word.zero` denotes a present
zero-balance account, so creation-era presence remains observable.
-/
def balanceEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option Core.Word × Option Core.Word :=
  (initialWorld.balance? address, finalWorld.balance? address)

/-- Observe exact creation-nonce endpoints at one address. -/
def nonceEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option Core.Word × Option Core.Word :=
  (initialWorld.nonce? address, finalWorld.nonce? address)

/-- Observe exact checked-code endpoints at one address. -/
def codeEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) :
    Option CheckedHostCoreProgram × Option CheckedHostCoreProgram :=
  (initialWorld.code? address, finalWorld.code? address)

/-- Report exactly an absent-to-present Account transition. -/
def createdAccount?
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Bool :=
  match initialWorld.account? address, finalWorld.account? address with
  | none, some _ => true
  | _, _ => false

/-- Return exact old/new storage endpoints only when the observation changed. -/
def slotChange?
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (slot : Core.Word) : Option (Option Core.Word × Option Core.Word) :=
  let endpoints := delta.storageEndpoints address slot
  if endpoints.1 = endpoints.2 then none else some endpoints

/-- Return exact old/new balance endpoints only when the observation changed. -/
def balanceChange?
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option (Option Core.Word × Option Core.Word) :=
  let endpoints := delta.balanceEndpoints address
  if endpoints.1 = endpoints.2 then none else some endpoints

/-- Return exact old/new nonce endpoints only when the observation changed. -/
def nonceChange?
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option (Option Core.Word × Option Core.Word) :=
  let endpoints := delta.nonceEndpoints address
  if endpoints.1 = endpoints.2 then none else some endpoints

end WorldStateDelta

end Solcore.ContractRuntime

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
