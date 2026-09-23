import Solcore.ContractRuntime.CheckedCoreProgram
import Solcore.Core.Machine

/-! Stateful Core-machine execution for checker-accepted programs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedCoreProgram

/-- Execute retained Core code without erasing its final Core-local store. -/
def runStateful
    (code : CheckedCoreProgram)
    (fuel : Nat) : Core.StatefulRunResult :=
  code.program.runStateful fuel

end Solcore.ContractRuntime.CheckedCoreProgram
