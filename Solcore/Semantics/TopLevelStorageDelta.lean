import Solcore.Semantics.WorldStateCode
import Solcore.Semantics.WorldStateStorageRead

/-! Exact queryable target-storage change across top-level finalization. -/

set_option autoImplicit false

namespace Solcore.Semantics

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

end Solcore.Semantics
