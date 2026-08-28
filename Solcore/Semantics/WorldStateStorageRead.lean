import Solcore.Semantics.WorldState

/-! Conditional storage reads over explicit WorldState account presence. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldState

/-- Read a slot only when its Account is explicitly present. -/
def readStorage?
    (state : WorldState)
    (address : Address)
    (slot : Core.Word) : Option Core.Word := do
  let account ← state.account? address
  some (account.storageRead slot)

end Solcore.Semantics.WorldState
