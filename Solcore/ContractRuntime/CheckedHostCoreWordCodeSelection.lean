import Solcore.ContractRuntime.CheckedHostCoreWordProgram

/-! Branch-complete refinement of optional checked code by Word result type. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- Exact absence, non-Word code, or Word-refined checked code. -/
inductive CheckedHostCoreWordCodeSelection where
  | codeAbsent
  | nonWord
      (code : CheckedHostCoreProgram)
      (resultType_ne_word : code.program.resultType ≠ .word)
  | word (code : CheckedHostCoreWordProgram)

namespace CheckedHostCoreWordCodeSelection

/-- Classify an existing optional checked-code observation without rerunning a checker. -/
def classify
    (selected : Option CheckedHostCoreProgram) :
    CheckedHostCoreWordCodeSelection :=
  match selected with
  | none => .codeAbsent
  | some code =>
      if resultTypeEq : code.program.resultType = .word then
        .word ⟨code, resultTypeEq⟩
      else
        .nonWord code resultTypeEq

/-- Erase only the Word-result refinement and recover existing code selection. -/
def toCheckedCode? :
    CheckedHostCoreWordCodeSelection → Option CheckedHostCoreProgram
  | .codeAbsent => none
  | .nonWord code _ => some code
  | .word code => some code.code

/-- Project checked Word code only from the exact Word branch. -/
def toWordCode? :
    CheckedHostCoreWordCodeSelection → Option CheckedHostCoreWordProgram
  | .word code => some code
  | .codeAbsent | .nonWord .. => none

end CheckedHostCoreWordCodeSelection

end Solcore.ContractRuntime
