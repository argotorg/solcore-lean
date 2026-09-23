import Solcore.ContractRuntime.WorldState

/-! Address-selected checked code lookup in explicit WorldState. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.WorldState

/-- Select host-checker-accepted code from the Account at one Address. -/
def code?
    (state : WorldState)
    (codeAddress : Address) : Option CheckedHostCoreProgram := do
  let account ← state.account? codeAddress
  account.code?

end Solcore.ContractRuntime.WorldState
