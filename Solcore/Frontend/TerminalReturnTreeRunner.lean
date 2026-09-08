import Solcore.Frontend.TerminalReturnTree

/-! Execute only the actual checked recursive Core with the original ordered
typed input values. No source-call or runtime-function profile is changed. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def checkTerminalReturnTree? (inputs : LocalInputs) (body : Syntax.Block) :
    Option (Core.Expr × Core.Ty) :=
  elaborateTerminalReturnTree? inputs.names inputs.context body

/-- Check failure is absent; a checked run retains its complete machine result,
including the genuine suspended state. Values are not reordered here. -/
def runTerminalReturnTree? (inputs : LocalInputs) (fuel : Nat) (body : Syntax.Block)
    (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let (core, type) ← inputs.checkTerminalReturnTree? body
  return (type, Core.runStateful fuel
    (Core.State.initial core (Resolved.LocalScope.values inputs.environment) store))

end Solcore.Frontend.LocalInputs
