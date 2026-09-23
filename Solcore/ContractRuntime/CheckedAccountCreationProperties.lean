import Solcore.ContractRuntime.CheckedAccountCreation

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
