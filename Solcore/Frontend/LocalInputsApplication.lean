import Solcore.Frontend.LocalInputs
import Solcore.Frontend.LocalFunctionApplication

/-! A separate checked application endpoint on the actual supplied input rows.
Check absence, runtime faults and fuel exhaustion remain distinct outcomes.
Structural input typing does not validate referenced cells or store payloads. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def checkApplication? (inputs : LocalInputs) (source : Syntax.Expr) : Option (Core.Expr × Core.Ty) :=
  elaborateLocalFunctionApplication? inputs.names inputs.context source

/-- Preserve the checked type tag and complete actual Core result. Typed
runtime-world/store premises belong to safety theorems, not this executable gate. -/
def runApplication? (inputs : LocalInputs) (fuel : Nat) (source : Syntax.Expr) (store : Core.Store) :
    Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkApplication? source
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end Solcore.Frontend.LocalInputs
