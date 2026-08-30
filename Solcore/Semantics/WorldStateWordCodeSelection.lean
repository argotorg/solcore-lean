import Solcore.Semantics.CheckedHostCoreWordCodeSelection
import Solcore.Semantics.WorldStateCode

/-! Address-selected checked Word-code classification in WorldState. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

/-- Classify the existing checked-code observation at one exact Address. -/
def selectWordCode
    (state : WorldState)
    (codeAddress : Address) :
    CheckedHostCoreWordCodeSelection :=
  CheckedHostCoreWordCodeSelection.classify
    (state.code? codeAddress)

end Solcore.Semantics.WorldState
