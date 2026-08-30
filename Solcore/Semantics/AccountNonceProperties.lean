import Solcore.Semantics.AccountBalanceProperties

/-! Nonce observations and preservation laws for Account updates. -/

set_option autoImplicit false

namespace Solcore.Semantics.Account

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

end Solcore.Semantics.Account
