import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.LocalInputsTypeErasure
import Solcore.Frontend.LocalInputsProperties
import Solcore.Core.Machine

/-! A separate checked body runner uses the actual static projection and the
original ordered values. It does not prepare or extend runtime function entries. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def checkTypedLetReturnBody? (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  elaborateTypedLetReturnBody? types owner inputs.toTypeInputs body

def runTypedLetReturnBody? (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkTypedLetReturnBody? types owner body
  return (type, Core.runStateful fuel (Core.State.initial core inputs.environment.values store))

end Solcore.Frontend.LocalInputs
