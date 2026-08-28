import Solcore.Semantics.WorldStateCode
import Solcore.Semantics.CheckedCoreProgramExecution

/-! Address-selected execution of checked closed Core code. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

/-- Execute selected code while retaining the complete Core-local run result. -/
def runCode?
    (state : WorldState)
    (codeAddress : Address)
    (fuel : Nat) : Option Core.StatefulRunResult :=
  (state.code? codeAddress).map fun code => code.runStateful fuel

end Solcore.Semantics.WorldState
