import Solcore.ContractRuntime.WorldStateCode
import Solcore.ContractRuntime.WorldStateStorageRead

/-! Exact queryable target-storage change across top-level finalization. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/--
An exact single-Account storage delta. The current function-valued WorldState
cannot enumerate changed slots, so callers query individual slots.
-/
structure TopLevelStorageDelta
    (initialWorld finalWorld : WorldState)
    (target : Address) where
  initialAccount : Account
  finalAccount : Account
  initialAccount_present :
    initialWorld.account? target = some initialAccount
  finalAccount_present :
    finalWorld.account? target = some finalAccount
  code_preserved : finalAccount.code? = initialAccount.code?
  otherAccounts_preserved :
    ∀ address, address ≠ target →
      finalWorld.account? address = initialWorld.account? address

namespace TopLevelStorageDelta

/-- Return exact old/new values only when the queried target slot changed. -/
def slotChange?
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) : Option (Core.Word × Core.Word) :=
  let before := delta.initialAccount.storageRead slot
  let after := delta.finalAccount.storageRead slot
  if before = after then none else some (before, after)

/-- The identity finalization has an exact empty queryable delta. -/
def identity
    (world : WorldState)
    (target : Address)
    (account : Account)
    (present : world.account? target = some account) :
    TopLevelStorageDelta world world target := {
  initialAccount := account
  finalAccount := account
  initialAccount_present := present
  finalAccount_present := present
  code_preserved := rfl
  otherAccounts_preserved := by
    intro _ _
    rfl
}

@[simp] theorem slotChange?_identity
    (world : WorldState)
    (target : Address)
    (account : Account)
    (present : world.account? target = some account)
    (slot : Core.Word) :
    (identity world target account present).slotChange? slot = none := by
  simp [slotChange?, identity]

end TopLevelStorageDelta

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.TopLevelStorageDeltaProperties`
-/

/-! Exact endpoint laws for queryable top-level storage deltas. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.TopLevelStorageDelta

/-- The endpoint worlds and target determine the storage-delta witness. -/
theorem unique
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (left right : TopLevelStorageDelta initialWorld finalWorld target) :
    left = right := by
  have initialAccount_eq : left.initialAccount = right.initialAccount := by
    apply Option.some.inj
    exact left.initialAccount_present.symm.trans right.initialAccount_present
  have finalAccount_eq : left.finalAccount = right.finalAccount := by
    apply Option.some.inj
    exact left.finalAccount_present.symm.trans right.finalAccount_present
  cases left
  cases right
  simp_all

theorem slotChange?_eq_none_iff
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    delta.slotChange? slot = none ↔
      delta.initialAccount.storageRead slot =
        delta.finalAccount.storageRead slot := by
  simp [slotChange?]

theorem slotChange?_eq_some_iff
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot before after : Core.Word) :
    delta.slotChange? slot = some (before, after) ↔
      delta.initialAccount.storageRead slot = before ∧
      delta.finalAccount.storageRead slot = after ∧
      before ≠ after := by
  unfold slotChange?
  by_cases same :
      delta.initialAccount.storageRead slot =
        delta.finalAccount.storageRead slot
  · simp [same]
    intro beforeEq afterEq
    exact beforeEq.symm.trans afterEq
  · simp only [if_neg same, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨beforeEq, afterEq⟩
      refine ⟨beforeEq, afterEq, ?_⟩
      intro valuesEqual
      apply same
      exact beforeEq.trans (valuesEqual.trans afterEq.symm)
    · rintro ⟨beforeEq, afterEq, _different⟩
      exact ⟨beforeEq, afterEq⟩

theorem finalWorld_code?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target) :
    finalWorld.code? target = initialWorld.code? target := by
  simp [WorldState.code?, delta.initialAccount_present,
    delta.finalAccount_present, delta.code_preserved]

theorem initialWorld_readStorage?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    initialWorld.readStorage? target slot =
      some (delta.initialAccount.storageRead slot) := by
  simp [WorldState.readStorage?, delta.initialAccount_present]

theorem finalWorld_readStorage?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    finalWorld.readStorage? target slot =
      some (delta.finalAccount.storageRead slot) := by
  simp [WorldState.readStorage?, delta.finalAccount_present]

end Solcore.ContractRuntime.TopLevelStorageDelta
