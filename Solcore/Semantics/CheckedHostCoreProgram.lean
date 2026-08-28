import Solcore.Core.Host

/-! Checker-accepted Core programs under the fixed host capability context. -/

set_option autoImplicit false

namespace Solcore.Semantics

structure CheckedHostCoreProgram where
  program : Core.Program
  checked : program.checkHost = true

namespace CheckedHostCoreProgram

def ofProgram? (program : Core.Program) : Option CheckedHostCoreProgram :=
  if checked : program.checkHost = true then
    some ⟨program, checked⟩
  else
    none

@[simp] theorem ofProgram?_of_checked
    (program : Core.Program)
    (checked : program.checkHost = true) :
    ofProgram? program = some ⟨program, checked⟩ := by
  simp [ofProgram?, checked]

@[simp] theorem ofProgram?_of_rejected
    (program : Core.Program)
    (rejected : program.checkHost = false) :
    ofProgram? program = none := by
  simp [ofProgram?, rejected]

end CheckedHostCoreProgram

end Solcore.Semantics
