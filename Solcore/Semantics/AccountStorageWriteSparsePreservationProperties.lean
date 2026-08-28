import Solcore.Semantics.WorldState

/-! Distinct-slot sparse-storage preservation for Account writes. -/

set_option autoImplicit false

namespace Solcore.Semantics

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

end Solcore.Semantics
