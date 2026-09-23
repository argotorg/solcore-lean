import Solcore.ContractRuntime.CheckedHostCoreWordCodeSelection
import Solcore.ContractRuntime.WorldStateCode
import Solcore.ContractRuntime.Account

/-! Address-selected checked Word-code classification in WorldState. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

/-- Classify the existing checked-code observation at one exact Address. -/
def selectWordCode
    (state : WorldState)
    (codeAddress : Address) :
    CheckedHostCoreWordCodeSelection :=
  CheckedHostCoreWordCodeSelection.classify
    (state.code? codeAddress)

end Solcore.ContractRuntime.WorldState

/-!
## Consolidated module: `Solcore.ContractRuntime.WorldStateWordCodeSelectionProperties`
-/

/-! Exact lookup and preservation laws for selected checked Word code. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

open CheckedHostCoreWordCodeSelection

/-- Erasing refinement recovers the canonical address-selected code lookup. -/
@[simp] theorem toCheckedCode?_selectWordCode
    (state : WorldState)
    (codeAddress : Address) :
    (state.selectWordCode codeAddress).toCheckedCode? =
      state.code? codeAddress := by
  exact toCheckedCode?_classify (state.code? codeAddress)

/-- Word projection is exactly optional refinement of the selected code. -/
@[simp] theorem toWordCode?_selectWordCode
    (state : WorldState)
    (codeAddress : Address) :
    (state.selectWordCode codeAddress).toWordCode? =
      (state.code? codeAddress).bind
        CheckedHostCoreWordProgram.ofChecked? := by
  exact toWordCode?_classify (state.code? codeAddress)

theorem selectWordCode_eq_codeAbsent_iff
    (state : WorldState)
    (codeAddress : Address) :
    state.selectWordCode codeAddress = .codeAbsent ↔
      state.code? codeAddress = none := by
  exact classify_eq_codeAbsent_iff (state.code? codeAddress)

theorem selectWordCode_eq_nonWord_iff
    (state : WorldState)
    (codeAddress : Address)
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word) :
    state.selectWordCode codeAddress = .nonWord code resultTypeNe ↔
      state.code? codeAddress = some code := by
  exact classify_eq_nonWord_iff
    (state.code? codeAddress) code resultTypeNe

theorem selectWordCode_eq_word_iff
    (state : WorldState)
    (codeAddress : Address)
    (code : CheckedHostCoreWordProgram) :
    state.selectWordCode codeAddress = .word code ↔
      state.code? codeAddress = some code.code := by
  exact classify_eq_word_iff (state.code? codeAddress) code

@[simp] theorem selectWordCode_of_absent
    (state : WorldState)
    (codeAddress : Address)
    (absent : state.account? codeAddress = none) :
    state.selectWordCode codeAddress = .codeAbsent := by
  apply (state.selectWordCode_eq_codeAbsent_iff codeAddress).2
  exact state.code?_of_absent codeAddress absent

@[simp] theorem selectWordCode_of_account_without_code
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (present : state.account? codeAddress = some account)
    (withoutCode : account.code? = none) :
    state.selectWordCode codeAddress = .codeAbsent := by
  apply (state.selectWordCode_eq_codeAbsent_iff codeAddress).2
  exact state.code?_of_account_without_code
    codeAddress account present withoutCode

@[simp] theorem selectWordCode_of_present_nonWord
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreProgram)
    (resultTypeNe : code.program.resultType ≠ .word)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code) :
    state.selectWordCode codeAddress = .nonWord code resultTypeNe := by
  apply (state.selectWordCode_eq_nonWord_iff
    codeAddress code resultTypeNe).2
  exact state.code?_of_present
    codeAddress account code accountPresent codePresent

@[simp] theorem selectWordCode_of_present_word
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (code : CheckedHostCoreWordProgram)
    (accountPresent : state.account? codeAddress = some account)
    (codePresent : account.code? = some code.code) :
    state.selectWordCode codeAddress = .word code := by
  apply (state.selectWordCode_eq_word_iff codeAddress code).2
  exact state.code?_of_present
    codeAddress account code.code accountPresent codePresent

@[simp] theorem selectWordCode_putAccount_same
    (state : WorldState)
    (codeAddress : Address)
    (account : Account) :
    (state.putAccount codeAddress account).selectWordCode codeAddress =
      classify account.code? := by
  simp [selectWordCode, code?, putAccount, account?]

/-- Writing Account storage cannot change its selected Word-code branch. -/
@[simp] theorem selectWordCode_putAccount_storageWrite_same
    (state : WorldState)
    (codeAddress : Address)
    (account : Account)
    (slot value : Core.Word) :
    (state.putAccount codeAddress
        (account.storageWrite slot value)).selectWordCode codeAddress =
      (state.putAccount codeAddress account).selectWordCode codeAddress := by
  simp [Account.code?_storageWrite]

end Solcore.ContractRuntime.WorldState
