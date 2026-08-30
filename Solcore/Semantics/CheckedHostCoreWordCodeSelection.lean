import Solcore.Semantics.CheckedHostCoreWordProgram

/-! Branch-complete refinement of optional checked code by Word result type. -/

set_option autoImplicit false

namespace Solcore.Semantics

/-- Exact absence, non-Word code, or Word-refined checked code. -/
inductive CheckedHostCoreWordCodeSelection where
  | absent
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
  | none => .absent
  | some code =>
      if resultTypeEq : code.program.resultType = .word then
        .word ⟨code, resultTypeEq⟩
      else
        .nonWord code resultTypeEq

/-- Erase only the Word-result refinement and recover existing code selection. -/
def toCheckedCode? :
    CheckedHostCoreWordCodeSelection → Option CheckedHostCoreProgram
  | .absent => none
  | .nonWord code _ => some code
  | .word code => some code.code

/-- Project checked Word code only from the exact Word branch. -/
def toWordCode? :
    CheckedHostCoreWordCodeSelection → Option CheckedHostCoreWordProgram
  | .word code => some code
  | .absent | .nonWord .. => none

end CheckedHostCoreWordCodeSelection

end Solcore.Semantics
