import Solcore.Semantics.WorldState

/-! Address-selected checked code lookup in explicit WorldState. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

/-- Select checker-accepted code from the Account at one Address. -/
def code?
    (state : WorldState)
    (codeAddress : Address) : Option CheckedCoreProgram := do
  let account ← state.account? codeAddress
  account.code?

end Solcore.Semantics.WorldState
