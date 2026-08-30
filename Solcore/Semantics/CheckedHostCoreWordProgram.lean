import Solcore.Semantics.CheckedHostCoreProgram

/-! Checker-accepted host-aware Core programs with Word result type. -/

set_option autoImplicit false

namespace Solcore.Semantics

/-- A checked host-aware program whose declared result is exactly Word. -/
structure CheckedHostCoreWordProgram where
  code : CheckedHostCoreProgram
  resultType_eq_word : code.program.resultType = .word

namespace CheckedHostCoreWordProgram

/-- Refine checked code exactly when its declared result type is Word. -/
def ofChecked? (code : CheckedHostCoreProgram) :
    Option CheckedHostCoreWordProgram :=
  if resultTypeEq : code.program.resultType = .word then
    some ⟨code, resultTypeEq⟩
  else
    none

/-- Check host admission and the Word result refinement together. -/
def ofProgram? (program : Core.Program) :
    Option CheckedHostCoreWordProgram := do
  let code ← CheckedHostCoreProgram.ofProgram? program
  ofChecked? code

end CheckedHostCoreWordProgram

end Solcore.Semantics
