import Solcore.ContractRuntime.WorldStateWordCodeSelectionProperties

/-! Compile-only consumers for branch-complete selected Word-code classification. -/

set_option autoImplicit false

namespace Solcore.Test.CheckedHostCoreWordCodeSelectionProperties

open ContractRuntime
open CheckedHostCoreWordCodeSelection

variable (checkedCode : CheckedHostCoreProgram)
variable (resultTypeEq : checkedCode.program.resultType = .word)
variable (resultTypeNe : checkedCode.program.resultType ≠ .word)
variable (wordCode : CheckedHostCoreWordProgram)
variable (selected : Option CheckedHostCoreProgram)
variable (selection left right : CheckedHostCoreWordCodeSelection)

example : classify none = .codeAbsent :=
  classify_none

example : classify (some checkedCode) =
    .word ⟨checkedCode, resultTypeEq⟩ :=
  classify_some_word checkedCode resultTypeEq

example : classify (some checkedCode) =
    .nonWord checkedCode resultTypeNe :=
  classify_some_nonWord checkedCode resultTypeNe

example : toCheckedCode? .codeAbsent = none :=
  toCheckedCode?_codeAbsent

example : toCheckedCode? (.nonWord checkedCode resultTypeNe) =
    some checkedCode :=
  toCheckedCode?_nonWord checkedCode resultTypeNe

example : toCheckedCode? (.word wordCode) = some wordCode.code :=
  toCheckedCode?_word wordCode

example : toWordCode? .codeAbsent = none :=
  toWordCode?_codeAbsent

example : toWordCode? (.nonWord checkedCode resultTypeNe) = none :=
  toWordCode?_nonWord checkedCode resultTypeNe

example : toWordCode? (.word wordCode) = some wordCode :=
  toWordCode?_word wordCode

example : toCheckedCode? (classify selected) = selected :=
  toCheckedCode?_classify selected

example : classify selection.toCheckedCode? = selection :=
  classify_toCheckedCode? selection

example (erased : left.toCheckedCode? = right.toCheckedCode?) :
    left = right :=
  toCheckedCode?_injective erased

example : toWordCode? (classify selected) =
    selected.bind CheckedHostCoreWordProgram.ofChecked? :=
  toWordCode?_classify selected

example : classify selected = .codeAbsent ↔ selected = none :=
  classify_eq_codeAbsent_iff selected

example : classify selected = .nonWord checkedCode resultTypeNe ↔
    selected = some checkedCode :=
  classify_eq_nonWord_iff selected checkedCode resultTypeNe

example : classify selected = .word wordCode ↔
    selected = some wordCode.code :=
  classify_eq_word_iff selected wordCode

example : CheckedHostCoreWordCodeSelection.codeAbsent ≠
    .nonWord checkedCode resultTypeNe :=
  codeAbsent_ne_nonWord checkedCode resultTypeNe

example : CheckedHostCoreWordCodeSelection.codeAbsent ≠ .word wordCode :=
  codeAbsent_ne_word wordCode

example : CheckedHostCoreWordCodeSelection.nonWord
      checkedCode resultTypeNe ≠ .word wordCode :=
  nonWord_ne_word checkedCode resultTypeNe wordCode

example : classify selected = .codeAbsent ∨
    (∃ code resultTypeNe,
      classify selected = .nonWord code resultTypeNe) ∨
    ∃ code, classify selected = .word code :=
  classify_exhaustive selected

variable (state : WorldState) (codeAddress : Address)

example : (state.selectWordCode codeAddress).toCheckedCode? =
    state.code? codeAddress :=
  WorldState.toCheckedCode?_selectWordCode state codeAddress

example : (state.selectWordCode codeAddress).toWordCode? =
    (state.code? codeAddress).bind
      CheckedHostCoreWordProgram.ofChecked? :=
  WorldState.toWordCode?_selectWordCode state codeAddress

example : state.selectWordCode codeAddress = .codeAbsent ↔
    state.code? codeAddress = none :=
  WorldState.selectWordCode_eq_codeAbsent_iff state codeAddress

example : state.selectWordCode codeAddress =
      .nonWord checkedCode resultTypeNe ↔
    state.code? codeAddress = some checkedCode :=
  WorldState.selectWordCode_eq_nonWord_iff
    state codeAddress checkedCode resultTypeNe

example : state.selectWordCode codeAddress = .word wordCode ↔
    state.code? codeAddress = some wordCode.code :=
  WorldState.selectWordCode_eq_word_iff state codeAddress wordCode

variable (account : Account)
variable (accountAbsent : state.account? codeAddress = none)
variable (accountPresent : state.account? codeAddress = some account)
variable (accountWithoutCode : account.code? = none)
variable (checkedCodePresent : account.code? = some checkedCode)
variable (wordCodePresent : account.code? = some wordCode.code)

example : state.selectWordCode codeAddress = .codeAbsent :=
  WorldState.selectWordCode_of_absent state codeAddress accountAbsent

example : state.selectWordCode codeAddress = .codeAbsent :=
  WorldState.selectWordCode_of_account_without_code
    state codeAddress account accountPresent accountWithoutCode

example : state.selectWordCode codeAddress =
    .nonWord checkedCode resultTypeNe :=
  WorldState.selectWordCode_of_present_nonWord
    state codeAddress account checkedCode resultTypeNe
      accountPresent checkedCodePresent

example : state.selectWordCode codeAddress = .word wordCode :=
  WorldState.selectWordCode_of_present_word
    state codeAddress account wordCode accountPresent wordCodePresent

example : (state.putAccount codeAddress account).selectWordCode codeAddress =
    classify account.code? :=
  WorldState.selectWordCode_putAccount_same state codeAddress account

variable (slot value : Core.Word)

example :
    (state.putAccount codeAddress
        (account.storageWrite slot value)).selectWordCode codeAddress =
      (state.putAccount codeAddress account).selectWordCode codeAddress :=
  WorldState.selectWordCode_putAccount_storageWrite_same
    state codeAddress account slot value

end Solcore.Test.CheckedHostCoreWordCodeSelectionProperties
