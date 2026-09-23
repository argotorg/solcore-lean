import Solcore.ContractRuntime.CheckedHostCoreProgram
import Solcore.Core.HostRunner

/-! Interactive execution for programs checked in the fixed host context. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CheckedHostCoreProgram

def runStateful
    (code : CheckedHostCoreProgram)
    (fuel : Nat) : Core.HostRunResult :=
  code.program.runHostStateful fuel

end Solcore.ContractRuntime.CheckedHostCoreProgram
