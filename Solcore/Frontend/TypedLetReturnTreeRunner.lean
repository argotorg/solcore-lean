import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.LocalInputsTypeErasure
import Solcore.Frontend.LocalInputsProperties
import Solcore.Core.Machine

/-! A separate recursive body runner checks the actual static projection and
executes the exact Core with the original ordered values. No function entry is
prepared or extended; branch-local bindings remain inside the checked body. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def checkTypedLetReturnTree? (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) : Option (Core.Expr × Core.Ty) :=
  elaborateTypedLetReturnTree? types owner inputs.toTypeInputs body

def runTypedLetReturnTree? (inputs : LocalInputs) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkTypedLetReturnTree? types owner body
  return (type, Core.runStateful fuel (Core.State.initial core inputs.environment.values store))

end Solcore.Frontend.LocalInputs
