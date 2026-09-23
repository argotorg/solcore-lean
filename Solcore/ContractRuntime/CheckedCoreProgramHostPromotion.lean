import Solcore.ContractRuntime.CheckedCoreProgram
import Solcore.ContractRuntime.CheckedHostCoreProgram

/-! Explicit promotion of closed checked code to the host-aware carrier. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CheckedCoreProgram

/-- Retain the exact program while admitting its unused host environment. -/
def toHost (code : CheckedCoreProgram) : CheckedHostCoreProgram :=
  ⟨code.program, Core.Program.checkHost_of_check code.checked⟩

@[simp] theorem toHost_program
    (code : CheckedCoreProgram) :
    code.toHost.program = code.program :=
  rfl

end CheckedCoreProgram

end Solcore.ContractRuntime
