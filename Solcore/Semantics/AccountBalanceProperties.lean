import Solcore.Semantics.AccountCodeProperties

/-! Balance observations and preservation laws for Account updates. -/

set_option autoImplicit false

namespace Solcore.Semantics.Account

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

end Solcore.Semantics.Account
