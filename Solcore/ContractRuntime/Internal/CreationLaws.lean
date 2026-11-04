import Solcore.ContractRuntime.Creation
import Solcore.ContractRuntime.Internal.WorldStateLaws
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.Internal.WorldStateDeltaLaws
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.ContractRuntime.StorageDriver
import Solcore.ContractRuntime.Internal.StorageDriverLaws
import Solcore.ContractRuntime.Contracts

/-!
# Laws of value transfer and creation

`WorldState.transferBalance` by cases, and the two creation preflights.
-/

section
-- leanmerge: from Solcore.ContractRuntime.BalanceTransfer
/-! Checked, non-wrapping balance transfer between present accounts. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferProperties`
-/

/-! Exact arithmetic and frame properties of checked balance transfer. -/
set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace Balance

theorem checkedDebit_eq_some_iff (balance amount result : Core.Word) :
    checkedDebit? balance amount = some result ↔
      amount.val ≤ balance.val ∧ result.val = balance.val - amount.val := by
  unfold checkedDebit?
  split
  · constructor
    · intro h; injection h with h
      exact ⟨by assumption, congrArg Fin.val h.symm⟩
    · rintro ⟨_, h⟩
      apply congrArg some
      apply Fin.ext
      exact h.symm
  · constructor
    · simp
    · intro facts
      omega

theorem checkedDebit_eq_none_iff (balance amount : Core.Word) :
    checkedDebit? balance amount = none ↔ balance.val < amount.val := by
  unfold checkedDebit?; split <;> simp_all

theorem checkedCredit_eq_some_iff (balance amount result : Core.Word) :
    checkedCredit? balance amount = some result ↔
      balance.val + amount.val < Core.wordModulus ∧
        result.val = balance.val + amount.val := by
  unfold checkedCredit? Core.Word.ofNat?
  split
  · constructor
    · intro h; injection h with h
      exact ⟨by assumption, congrArg Fin.val h.symm⟩
    · rintro ⟨_, h⟩
      apply congrArg some
      apply Fin.ext
      exact h.symm
  · constructor
    · simp
    · intro facts
      omega

theorem checkedCredit_eq_none_iff (balance amount : Core.Word) :
    checkedCredit? balance amount = none ↔
      Core.wordModulus ≤ balance.val + amount.val := by
  unfold checkedCredit? Core.Word.ofNat?; split <;> simp_all

end Balance

namespace WorldState

theorem transferBalance_senderAbsent (state : WorldState)
    (sender recipient : Address) (amount : Core.Word)
    (h : state.account? sender = none) :
    state.transferBalance sender recipient amount = .error .senderAbsent := by
  simp [transferBalance, h]

theorem transferBalance_recipientAbsent (state : WorldState)
    (sender recipient : Address) (amount : Core.Word) (senderAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = none) :
    state.transferBalance sender recipient amount = .error .recipientAbsent := by
  simp [transferBalance, hs, hr]

theorem transferBalance_insufficient (state : WorldState)
    (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (h : senderAccount.balance.val < amount.val) :
    state.transferBalance sender recipient amount = .error .insufficientBalance := by
  have hd := (Balance.checkedDebit_eq_none_iff senderAccount.balance amount).2 h
  rw [transferBalance]; simp [hs, hr, hd]

theorem transferBalance_zero (state : WorldState) (sender recipient : Address)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount) :
    state.transferBalance sender recipient Core.Word.zero = .ok state := by
  rw [transferBalance]; simp only [hs, hr]
  have hd : Balance.checkedDebit? senderAccount.balance Core.Word.zero =
      some senderAccount.balance := by
    apply (Balance.checkedDebit_eq_some_iff _ _ _).2
    change 0 ≤ senderAccount.balance.val ∧
      senderAccount.balance.val = senderAccount.balance.val - 0
    omega
  simp [hd]

theorem transferBalance_self (state : WorldState) (address : Address)
    (amount : Core.Word) (account : Account)
    (hp : state.account? address = some account)
    (h : amount.val ≤ account.balance.val) :
    state.transferBalance address address amount = .ok state := by
  rw [transferBalance]; simp only [hp]
  unfold Balance.checkedDebit?; simp [h]

theorem transferBalance_overflow (state : WorldState)
    (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (sufficient : amount.val ≤ senderAccount.balance.val)
    (nonzero : amount ≠ Core.Word.zero) (different : sender ≠ recipient)
    (overflow : Core.wordModulus ≤ recipientAccount.balance.val + amount.val) :
    state.transferBalance sender recipient amount = .error .recipientOverflow := by
  rw [transferBalance]; simp only [hs, hr]
  unfold Balance.checkedDebit?
  have hc := (Balance.checkedCredit_eq_none_iff recipientAccount.balance amount).2
    overflow
  simp [sufficient, nonzero, different, hc]

theorem transferBalance_cross_eq (state : WorldState)
    (sender recipient : Address) (amount : Core.Word)
    (senderAccount recipientAccount : Account)
    (hs : state.account? sender = some senderAccount)
    (hr : state.account? recipient = some recipientAccount)
    (debited credited : Core.Word)
    (hd : Balance.checkedDebit? senderAccount.balance amount = some debited)
    (hc : Balance.checkedCredit? recipientAccount.balance amount = some credited)
    (nonzero : amount ≠ Core.Word.zero) (different : sender ≠ recipient) :
    state.transferBalance sender recipient amount = .ok
      ((state.putAccount sender (senderAccount.withBalance debited)).putAccount
        recipient (recipientAccount.withBalance credited)) := by
  simp [transferBalance, hs, hr, hd, hc, nonzero, different]

theorem transferBalance_cross_balances (state : WorldState)
    (sender recipient : Address) (senderAccount recipientAccount : Account)
    (debited credited : Core.Word) (different : sender ≠ recipient) :
    let next := (state.putAccount sender (senderAccount.withBalance debited)).putAccount
      recipient (recipientAccount.withBalance credited)
    next.balance? sender = some debited ∧ next.balance? recipient = some credited := by
  dsimp; constructor
  · rw [balance?_putAccount_other _ recipient sender _ different]; simp
  · simp

theorem transferBalance_cross_conserves
    (senderBalance recipientBalance amount debited credited : Core.Word)
    (hd : Balance.checkedDebit? senderBalance amount = some debited)
    (hc : Balance.checkedCredit? recipientBalance amount = some credited) :
    debited.val + credited.val = senderBalance.val + recipientBalance.val := by
  have hd' := (Balance.checkedDebit_eq_some_iff _ _ _).1 hd
  have hc' := (Balance.checkedCredit_eq_some_iff _ _ _).1 hc
  omega

end WorldState

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferInstallationProperties`
-/

/-! Checked contract installation survives balance-only state transitions. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferPresenceProperties`
-/

/-! Account presence survives successful balance-only transitions. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferCallFailure`
-/

/-! Stable checked-call failures for total balance-transfer failures. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.BalanceTransferCallFailureProperties`
-/

/-! Exact failure translation laws for value-bearing checked calls. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.BalanceTransferFailure

@[simp] theorem toContractCallFailure_senderAbsent :
    senderAbsent.toContractCallFailure = .unavailable :=
  rfl

@[simp] theorem toContractCallFailure_recipientAbsent :
    recipientAbsent.toContractCallFailure = .unavailable :=
  rfl

@[simp] theorem toContractCallFailure_insufficientBalance :
    insufficientBalance.toContractCallFailure = .insufficientBalance :=
  rfl

@[simp] theorem toContractCallFailure_recipientOverflow :
    recipientOverflow.toContractCallFailure = .balanceOverflow :=
  rfl

@[simp] theorem toContractCallResult_code (failure : BalanceTransferFailure) :
    failure.toContractCallResult =
      .failed failure.toContractCallFailure.code :=
  rfl

end Solcore.ContractRuntime.BalanceTransferFailure
end

section
-- leanmerge: from Solcore.ContractRuntime.CheckedAccountCreation
/-! Total state preparation for checked contract-account creation. -/

set_option autoImplicit false

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
end

section
-- leanmerge: from Solcore.ContractRuntime.CheckedCreationPreflight
/-! Immutable-environment validation and total checked creation preflight. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCreationPreflightProperties`
-/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace RegisteredCreationRuntime

@[simp] theorem validate?_lookup_none (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (h : e.callRegistry.lookup a = none) :
    validate? e a t = none := by
  unfold validate?; split
  · rfl
  · simp_all

@[simp] theorem validate?_program_mismatch (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (c : CheckedCoreContract)
    (hl : e.callRegistry.lookup a = some c)
    (hp : c.code.program ≠ t.runtime.code.program) : validate? e a t = none := by
  unfold validate?; split
  · simp_all
  · rename_i found heq
    have : found = c := Option.some.inj (heq.symm.trans hl)
    subst found
    simp [hp]

theorem validate?_some_program_eq (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (r : RegisteredCreationRuntime e a t)
    (_h : validate? e a t = some r) :
    r.contract.code.program = t.runtime.code.program := r.program_eq

end RegisteredCreationRuntime

namespace CheckedCreationPreflight

@[simp] theorem prepare_templateUnavailable (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (h : e.creationTemplates.lookup id = none) :
    prepare s e creator id value = .error .unavailable := by
  unfold prepare; split
  · rfl
  · simp_all

@[simp] theorem prepare_creatorUnavailable (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (t : CheckedCreationTemplate) (ht : e.creationTemplates.lookup id = some t)
    (ha : s.account? creator = none) :
    prepare s e creator id value = .error .unavailable := by
  unfold prepare; split
  · simp_all
  · rename_i actual heq
    have : actual = t := Option.some.inj (heq.symm.trans ht)
    subst actual
    split <;> simp_all

@[simp] theorem prepare_nonceOverflow (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (t : CheckedCreationTemplate) (account : Account)
    (ht : e.creationTemplates.lookup id = some t)
    (ha : s.account? creator = some account)
    (ho : account.incrementNonce? = none) :
    prepare s e creator id value = .error .nonceOverflow := by
  unfold prepare; split
  · simp_all
  · rename_i actualT teq
    have : actualT = t := Option.some.inj (teq.symm.trans ht); subst actualT
    split
    · simp_all
    · rename_i actualA aeq
      have : actualA = account := Option.some.inj (aeq.symm.trans ha); subst actualA
      split <;> simp_all

theorem PreparedCheckedCreation.runtime_exact
    {s : WorldState} {e : ExecutionEnvironment} {creator : Address}
    {id value : Core.Word} (p : PreparedCheckedCreation s e creator id value) :
    p.runtimeRegistration.contract = p.template.runtime := p.runtimeRegistration.contract_eq

theorem PreparedCheckedCreation.address_exact
    {s : WorldState} {e : ExecutionEnvironment} {creator : Address}
    {id value : Core.Word} (p : PreparedCheckedCreation s e creator id value) :
    p.statePreparation.createdAddress =
      e.creationAddressPolicy.derive creator p.oldNonce := by
  rw [p.preparation_address_eq, p.createdAddress_eq]

end CheckedCreationPreflight

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCreationPreflightFailure`
-/

/-! Stable call-result injection for checked creation preflight failures. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.CheckedCreationPreflightFailureProperties`
-/

/-! Exact stable codes for checked creation preflight failure injection. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedCreationPreflightFailure

@[simp] theorem unavailable_code :
    CheckedCreationPreflightFailure.unavailable.toContractCallFailure.code =
      ⟨1, by decide⟩ := by
  rfl

@[simp] theorem nonceOverflow_code :
    CheckedCreationPreflightFailure.nonceOverflow.toContractCallFailure.code =
      ⟨5, by decide⟩ := by
  rfl

@[simp] theorem addressCollision_code :
    CheckedCreationPreflightFailure.addressCollision.toContractCallFailure.code =
      ⟨6, by decide⟩ := by
  rfl

@[simp] theorem transfer_code (failure : BalanceTransferFailure) :
    (CheckedCreationPreflightFailure.transfer failure).toContractCallFailure =
      failure.toContractCallFailure := by
  rfl

@[simp] theorem result_value (failure : CheckedCreationPreflightFailure) :
    failure.toContractCallResult.value =
      .inRight .word
        (.inRight .word
          (.inRight .word
            (.word failure.toContractCallFailure.code))) := by
  cases failure <;> rfl

@[simp] theorem result_response (failure : CheckedCreationPreflightFailure) :
    Core.HostRequest.responseValue
        (.createContractWord Core.Word.zero Core.Word.zero Core.Word.zero)
        failure.toContractCallResult =
      failure.toContractCallResult.value := by
  rfl

end Solcore.ContractRuntime.CheckedCreationPreflightFailure
end
