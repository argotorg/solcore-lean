import Solcore.ContractRuntime.WorldState

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
