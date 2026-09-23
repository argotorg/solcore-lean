import Solcore.Core.Typing

/-! Checker-accepted closed Core programs retained by contract semantics. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A closed Core program together with its executable checker evidence. -/
structure CheckedCoreProgram where
  program : Core.Program
  checked : program.check = true

namespace CheckedCoreProgram

/-- Admit exactly the programs accepted by the existing Core checker. -/
def ofProgram? (program : Core.Program) : Option CheckedCoreProgram :=
  if checked : program.check = true then
    some ⟨program, checked⟩
  else
    none

end CheckedCoreProgram

end Solcore.ContractRuntime
