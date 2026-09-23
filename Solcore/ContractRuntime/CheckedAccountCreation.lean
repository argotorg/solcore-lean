import Solcore.ContractRuntime.Account
import Solcore.ContractRuntime.BalanceTransfer
import Solcore.ContractRuntime.CreationAddressPolicy

/-! Total state preparation for checked contract-account creation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Ordered, total failures of creation preflight. -/
inductive CreationPreflightFailure where
  | creatorAbsent
  | nonceOverflow
  | addressCollision
  | transfer (failure : BalanceTransferFailure)
  deriving Repr, BEq, DecidableEq

/--
Exact evidence for every intermediate state produced before initializer
execution. No field is inferred from a later world: the old nonce, derived
address, increment, collision check, provisional insertion, and value transfer
are all retained explicitly.
-/
structure PreparedAccountCreation
    (current : WorldState)
    (policy : CreationAddressPolicy)
    (creator : Address)
    (value : Core.Word)
    (initializer : CheckedCoreContract) where
  creatorAccount : Account
  creator_present : current.account? creator = some creatorAccount
  oldNonce : Core.Word
  oldNonce_eq : oldNonce = creatorAccount.nonce
  createdAddress : Address
  createdAddress_eq : createdAddress = policy.derive creator oldNonce
  incrementedCreator : Account
  increment_eq : creatorAccount.incrementNonce? = some incrementedCreator
  created_absent : current.account? createdAddress = none
  postNonceWorld : WorldState
  postNonceWorld_eq :
    postNonceWorld = current.putAccount creator incrementedCreator
  provisionalAccount : Account
  provisionalAccount_eq :
    provisionalAccount = Account.empty.withCode initializer.code
  provisionalWorld : WorldState
  provisionalWorld_eq :
    provisionalWorld = postNonceWorld.putAccount createdAddress provisionalAccount
  initializerWorld : WorldState
  transfer_eq :
    provisionalWorld.transferBalance creator createdAddress value =
      .ok initializerWorld
  initializerInstalled :
    InstalledCheckedCoreContract initializerWorld createdAddress initializer

namespace CheckedAccountCreation

/--
Prepare a creation transaction in consensus order. Every failure returns before
publishing a successor world; successful value movement is checked and exact.
-/
def prepare
    (current : WorldState)
    (policy : CreationAddressPolicy)
    (creator : Address)
    (value : Core.Word)
    (initializer : CheckedCoreContract) :
    Except CreationPreflightFailure
      (PreparedAccountCreation current policy creator value initializer) :=
  match creatorEq : current.account? creator with
  | none => .error .creatorAbsent
  | some creatorAccount =>
      let oldNonce := creatorAccount.nonce
      let createdAddress := policy.derive creator oldNonce
      match incrementEq : creatorAccount.incrementNonce? with
      | none => .error .nonceOverflow
      | some incrementedCreator =>
          match absentEq : current.account? createdAddress with
          | some _ => .error .addressCollision
          | none =>
              let postNonceWorld :=
                current.putAccount creator incrementedCreator
              let provisionalAccount :=
                Account.empty.withCode initializer.code
              let provisionalWorld :=
                postNonceWorld.putAccount createdAddress provisionalAccount
              let provisionalInstalled :
                  InstalledCheckedCoreContract provisionalWorld createdAddress
                    initializer := {
                account := provisionalAccount
                account_present := by
                  exact WorldState.account?_putAccount_same _ _ _
                code_present := by rfl
              }
              match transferEq : provisionalWorld.transferBalance creator
                  createdAddress value with
              | .error failure => .error (.transfer failure)
              | .ok initializerWorld =>
                  .ok {
                    creatorAccount := creatorAccount
                    creator_present := creatorEq
                    oldNonce := oldNonce
                    oldNonce_eq := rfl
                    createdAddress := createdAddress
                    createdAddress_eq := rfl
                    incrementedCreator := incrementedCreator
                    increment_eq := incrementEq
                    created_absent := absentEq
                    postNonceWorld := postNonceWorld
                    postNonceWorld_eq := rfl
                    provisionalAccount := provisionalAccount
                    provisionalAccount_eq := rfl
                    provisionalWorld := provisionalWorld
                    provisionalWorld_eq := rfl
                    initializerWorld := initializerWorld
                    transfer_eq := transferEq
                    initializerInstalled :=
                      WorldState.transferBalance_preserves_installed transferEq
                        provisionalInstalled
                  }

end CheckedAccountCreation
end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedAccountCreationProperties`
-/

/-! Branch and evidence laws for checked account-creation preparation. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime
namespace CheckedAccountCreation

@[simp] theorem prepare_creatorAbsent
    (current : WorldState) (policy : CreationAddressPolicy)
    (creator : Address) (value : Core.Word)
    (initializer : CheckedCoreContract)
    (absent : current.account? creator = none) :
    prepare current policy creator value initializer =
      .error .creatorAbsent := by
  unfold prepare
  split
  · rfl
  · rename_i account present
    rw [absent] at present
    contradiction

@[simp] theorem prepare_nonceOverflow
    (current : WorldState) (policy : CreationAddressPolicy)
    (creator : Address) (value : Core.Word)
    (initializer : CheckedCoreContract) (creatorAccount : Account)
    (present : current.account? creator = some creatorAccount)
    (overflow : creatorAccount.incrementNonce? = none) :
    prepare current policy creator value initializer =
      .error .nonceOverflow := by
  unfold prepare
  split
  · rename_i absent
    rw [present] at absent
    contradiction
  · rename_i found creatorEq
    have equal : found = creatorAccount := Option.some.inj
      (creatorEq.symm.trans present)
    subst found
    split
    · rfl
    · rename_i incremented incrementedEq
      rw [overflow] at incrementedEq
      contradiction

theorem PreparedAccountCreation.increment_exact
    {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.incrementedCreator.nonce.val =
      prepared.oldNonce.val + 1 := by
  rw [prepared.oldNonce_eq]
  exact Account.incrementNonce?_success_exact _ _ prepared.increment_eq

theorem PreparedAccountCreation.created_ne_creator
    {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.createdAddress ≠ creator := by
  intro equal
  have absent := prepared.created_absent
  rw [equal, prepared.creator_present] at absent
  contradiction

theorem PreparedAccountCreation.increment_preserves_creator_payload
    {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.incrementedCreator.code? = prepared.creatorAccount.code? ∧
      (∀ slot, prepared.incrementedCreator.storageValue? slot =
        prepared.creatorAccount.storageValue? slot) ∧
      prepared.incrementedCreator.balance = prepared.creatorAccount.balance :=
  by
    rcases Account.incrementNonce?_preserves_payload _ _ prepared.increment_eq with
      ⟨balance, code, storage⟩
    exact ⟨code, storage, balance⟩

@[simp] theorem PreparedAccountCreation.postNonce_creator
    {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.postNonceWorld.account? creator =
      some prepared.incrementedCreator := by
  rw [prepared.postNonceWorld_eq]
  exact WorldState.account?_putAccount_same _ _ _

@[simp] theorem PreparedAccountCreation.provisional_created
    {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.provisionalWorld.account? prepared.createdAddress =
      some prepared.provisionalAccount := by
  rw [prepared.provisionalWorld_eq]
  exact WorldState.account?_putAccount_same _ _ _

theorem PreparedAccountCreation.initializer_code_installed
    {current : WorldState} {policy : CreationAddressPolicy}
    {creator : Address} {value : Core.Word}
    {initializer : CheckedCoreContract}
    (prepared :
      PreparedAccountCreation current policy creator value initializer) :
    prepared.initializerInstalled.account.code? = some initializer.code :=
  prepared.initializerInstalled.code_present

end CheckedAccountCreation
end Solcore.ContractRuntime
