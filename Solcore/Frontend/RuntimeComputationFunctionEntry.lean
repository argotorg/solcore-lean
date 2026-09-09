import Solcore.Frontend.RuntimeFunctionEntry
import Solcore.Frontend.LocalComputationReturnTree

/-! Original actual arguments prepare a separate mixed-body entry. The same
input record supplies the type-only view and the actual runtime environment. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeComputationFunctionPrepares (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature prepared.returnType
  parameters : RuntimeParametersBind types owner declaration.value.signature.parameters.elements
    arguments prepared.inputs
  body : LocalComputationReturnTreeElaborates types owner prepared.inputs.toTypeInputs
    declaration.value.body prepared.core prepared.returnType

def prepareRuntimeComputationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option PreparedRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
  let (core, inferredType) ← elaborateLocalComputationReturnTree? types owner inputs.toTypeInputs declaration.value.body
  if inferredType = returnType then return { inputs, core, returnType }
  else none

/-- The separately supplied store is not checked by structural preparation.
Keep every present Core result, including faults and actual suspended states. -/
def runRuntimeComputationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let prepared ← prepareRuntimeComputationFunction? types owner declaration arguments
  return (prepared.returnType, Core.runStateful fuel
    (Core.State.initial prepared.core prepared.inputs.environment.values store))

end Solcore.Frontend
