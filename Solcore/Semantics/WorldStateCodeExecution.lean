import Solcore.Semantics.WorldStateCode
import Solcore.Semantics.CheckedHostCoreProgramExecution

/-! Address-selected execution until the first host boundary. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

/-- Execute selected host-aware code until completion or its first boundary. -/
def runCode?
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat) : Option Core.HostRunResult :=
  (state.code? codeAddress).map fun code => code.runStateful fuel

end Solcore.Semantics.WorldState
