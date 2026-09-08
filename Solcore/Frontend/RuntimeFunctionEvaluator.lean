import Solcore.Frontend.RuntimeFunctionEntry
import Solcore.Frontend.TypedLetReturnTreeEvaluator

/-! The existing whole-entry gate retains all header, argument and return checks.
It performs static lowering; actual result computation follows the original body
directly and never executes the prepared Core or rebinds the arguments. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Return the declared type, actual value and exact existing transition cost.
Successful preparation supplies the original parameter-only input bundle. -/
def evaluateRuntimeFunctionWithCost? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option (Core.Ty × Core.Value × Nat) := do
  let prepared ← prepareRuntimeFunction? types owner declaration arguments
  let (value, cost) ← evaluateTypedLetReturnTreeWithCost? owner
    prepared.inputs.names prepared.inputs.environment declaration.value.body
  return (prepared.returnType, value, cost)

end Solcore.Frontend
