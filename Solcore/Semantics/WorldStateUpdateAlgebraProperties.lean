import Solcore.Semantics.WorldStateExtensionalityProperties

set_option autoImplicit false

namespace Solcore.Semantics

@[simp] theorem Account.storageWrite_overwrite
    (account : Account)
    (slot first second : Core.Word) :
    (account.storageWrite slot first).storageWrite slot second =
      account.storageWrite slot second := by
  apply Account.ext
  · intro current
    by_cases firstZero : first = Core.Word.zero
    <;> by_cases secondZero : second = Core.Word.zero
    <;> by_cases selected : current = slot
    <;> simp [Account.storageWrite, Account.storageValue?, firstZero,
      secondZero, selected]
  · by_cases firstZero : first = Core.Word.zero
    <;> by_cases secondZero : second = Core.Word.zero
    <;> simp [Account.storageWrite, Account.code?, firstZero, secondZero]

theorem Account.storageWrite_commute
    (account : Account)
    (leftSlot leftValue rightSlot rightValue : Core.Word)
    (different : leftSlot ≠ rightSlot) :
    (account.storageWrite leftSlot leftValue).storageWrite
        rightSlot rightValue =
      (account.storageWrite rightSlot rightValue).storageWrite
        leftSlot leftValue := by
  have reverse : rightSlot ≠ leftSlot := Ne.symm different
  apply Account.ext
  · intro current
    by_cases leftZero : leftValue = Core.Word.zero
    <;> by_cases rightZero : rightValue = Core.Word.zero
    <;> by_cases atLeft : current = leftSlot
    <;> by_cases atRight : current = rightSlot
    <;> simp [Account.storageWrite, Account.storageValue?, leftZero, rightZero,
      atLeft, atRight, different, reverse]
  · by_cases leftZero : leftValue = Core.Word.zero
    <;> by_cases rightZero : rightValue = Core.Word.zero
    <;> simp [Account.storageWrite, Account.code?, leftZero, rightZero]

@[simp] theorem WorldState.putAccount_overwrite
    (state : WorldState)
    (address : Address)
    (first second : Account) :
    (state.putAccount address first).putAccount address second =
      state.putAccount address second := by
  apply WorldState.ext
  intro current
  by_cases selected : current = address
  <;> simp [WorldState.putAccount, WorldState.account?, selected]

theorem WorldState.putAccount_commute
    (state : WorldState)
    (leftAddress rightAddress : Address)
    (leftAccount rightAccount : Account)
    (different : leftAddress ≠ rightAddress) :
    (state.putAccount leftAddress leftAccount).putAccount
        rightAddress rightAccount =
      (state.putAccount rightAddress rightAccount).putAccount
        leftAddress leftAccount := by
  have reverse : rightAddress ≠ leftAddress := Ne.symm different
  apply WorldState.ext
  intro current
  by_cases atLeft : current = leftAddress
  <;> by_cases atRight : current = rightAddress
  <;> simp [WorldState.putAccount, WorldState.account?, atLeft, atRight,
    different, reverse]

end Solcore.Semantics
