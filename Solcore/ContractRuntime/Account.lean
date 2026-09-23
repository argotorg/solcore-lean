import Solcore.ContractRuntime.WorldState

/-! Account code, balance, nonce, and sparse-storage laws. -/

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountCodeProperties`
-/

/-! Checked-code observations and storage preservation for Account. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

@[simp] theorem code?_empty : Account.empty.code? = none := by
  rfl

@[simp] theorem code?_withCode
    (account : Account)
    (code : CheckedHostCoreProgram) :
    (account.withCode code).code? = some code := by
  rfl

@[simp] theorem storageValue?_withCode
    (account : Account)
    (code : CheckedHostCoreProgram)
    (slot : Core.Word) :
    (account.withCode code).storageValue? slot = account.storageValue? slot := by
  rfl

@[simp] theorem code?_storageWrite
    (account : Account)
    (slot value : Core.Word) :
    (account.storageWrite slot value).code? = account.code? := by
  by_cases zero : value = Core.Word.zero
  · simp [storageWrite, code?, zero]
  · simp [storageWrite, code?, zero]

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountBalanceProperties`
-/

/-! Balance observations and preservation laws for Account updates. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

@[simp] theorem balance_empty : Account.empty.balance = Core.Word.zero := by
  rfl

@[simp] theorem balance_withBalance
    (account : Account)
    (balance : Core.Word) :
    (account.withBalance balance).balance = balance := by
  rfl

@[simp] theorem storageValue?_withBalance
    (account : Account)
    (balance : Core.Word)
    (slot : Core.Word) :
    (account.withBalance balance).storageValue? slot =
      account.storageValue? slot := by
  rfl

@[simp] theorem code?_withBalance
    (account : Account)
    (balance : Core.Word) :
    (account.withBalance balance).code? = account.code? := by
  rfl

@[simp] theorem balance_withCode
    (account : Account)
    (code : CheckedHostCoreProgram) :
    (account.withCode code).balance = account.balance := by
  rfl

@[simp] theorem balance_storageWrite
    (account : Account)
    (slot value : Core.Word) :
    (account.storageWrite slot value).balance = account.balance := by
  by_cases zero : value = Core.Word.zero
  · simp [storageWrite, balance, zero]
  · simp [storageWrite, balance, zero]

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountNonceProperties`
-/

/-! Nonce observations and preservation laws for Account updates. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

@[simp] theorem nonce_empty : Account.empty.nonce = Core.Word.zero := by
  rfl

@[simp] theorem nonce_withNonce
    (account : Account)
    (nonce : Core.Word) :
    (account.withNonce nonce).nonce = nonce := by
  rfl

@[simp] theorem storageValue?_withNonce
    (account : Account)
    (nonce slot : Core.Word) :
    (account.withNonce nonce).storageValue? slot =
      account.storageValue? slot := by
  rfl

@[simp] theorem code?_withNonce
    (account : Account)
    (nonce : Core.Word) :
    (account.withNonce nonce).code? = account.code? := by
  rfl

@[simp] theorem balance_withNonce
    (account : Account)
    (nonce : Core.Word) :
    (account.withNonce nonce).balance = account.balance := by
  rfl

@[simp] theorem nonce_withBalance
    (account : Account)
    (balance : Core.Word) :
    (account.withBalance balance).nonce = account.nonce := by
  rfl

@[simp] theorem nonce_withCode
    (account : Account)
    (code : CheckedHostCoreProgram) :
    (account.withCode code).nonce = account.nonce := by
  rfl

@[simp] theorem nonce_storageWrite
    (account : Account)
    (slot value : Core.Word) :
    (account.storageWrite slot value).nonce = account.nonce := by
  by_cases zero : value = Core.Word.zero
  · simp [storageWrite, nonce, zero]
  · simp [storageWrite, nonce, zero]

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountNonceIncrement`
-/

/-! Checked, non-wrapping account nonce increment. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

/-- Increment the nonce exactly once, failing instead of wrapping at 2^256. -/
def incrementNonce? (account : Account) : Option Account := do
  let next ← Core.Word.ofNat? (account.nonce.val + 1)
  some (account.withNonce next)

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountNonceIncrementProperties`
-/

/-! Exact arithmetic and payload laws for checked nonce increment. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.Account

theorem incrementNonce?_isSome_iff (account : Account) :
    account.incrementNonce?.isSome ↔
      account.nonce.val + 1 < Core.wordModulus := by
  unfold incrementNonce? Core.Word.ofNat?
  split <;> simp_all

theorem incrementNonce?_eq_none_iff (account : Account) :
    account.incrementNonce? = none ↔
      Core.wordModulus ≤ account.nonce.val + 1 := by
  simp [incrementNonce?, Core.Word.ofNat?, Nat.not_lt]

theorem incrementNonce?_success_exact
    (account next : Account)
    (success : account.incrementNonce? = some next) :
    next.nonce.val = account.nonce.val + 1 := by
  unfold incrementNonce? Core.Word.ofNat? at success
  split at success
  · injection success with equal
    subst next
    simp
  · contradiction

@[simp] theorem incrementNonce?_maximum (account : Account) :
    (account.withNonce Core.Word.maximum).incrementNonce? = none := by
  apply (incrementNonce?_eq_none_iff _).2
  change Core.wordModulus ≤ (Core.wordModulus - 1) + 1
  omega

theorem incrementNonce?_preserves_payload
    (account next : Account)
    (success : account.incrementNonce? = some next) :
    next.balance = account.balance ∧
      next.code? = account.code? ∧
      ∀ slot, next.storageValue? slot = account.storageValue? slot := by
  unfold incrementNonce? Core.Word.ofNat? at success
  split at success
  · injection success with equal
    subst next
    simp
  · contradiction

theorem incrementNonce?_success_iff (account : Account) :
    (∃ next, account.incrementNonce? = some next ∧
      next.nonce.val = account.nonce.val + 1) ↔
      account.nonce.val + 1 < Core.wordModulus := by
  constructor
  · rintro ⟨next, success, _⟩
    exact (incrementNonce?_isSome_iff account).1 (by simp [success])
  · intro inBounds
    let nextNonce : Core.Word := ⟨account.nonce.val + 1, inBounds⟩
    refine ⟨account.withNonce nextNonce, ?_, ?_⟩
    · simp [incrementNonce?, Core.Word.ofNat?, inBounds, nextNonce]
    · simp [nextNonce]

end Solcore.ContractRuntime.Account

/-!
## Consolidated module: `Solcore.ContractRuntime.AccountStorageWriteSparsePreservationProperties`
-/

/-! Distinct-slot sparse-storage preservation for Account writes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A storage write preserves the optional sparse entry at every other slot. -/
theorem Account.storageValue?_storageWrite_other
    (account : Account)
    (writtenSlot value otherSlot : Core.Word)
    (different : otherSlot ≠ writtenSlot) :
    (account.storageWrite writtenSlot value).storageValue? otherSlot =
      account.storageValue? otherSlot := by
  by_cases zero : value = Core.Word.zero
  · simp [Account.storageWrite, Account.storageValue?, zero, different]
  · simp [Account.storageWrite, Account.storageValue?, zero, different]

end Solcore.ContractRuntime
