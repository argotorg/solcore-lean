import Solcore.Frontend.RuntimeFunctionEntry
import Solcore.Frontend.LocalApplicationReturnBody

/-! A separate explicit whole-function entry using the original actual typed
arguments. Header, parameter and exact body evidence belong to this profile,
not to the unchanged pure/recursive entry sharing the data-only output record. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeApplicationFunctionPrepares (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature prepared.returnType
  parameters : RuntimeParametersBind types owner declaration.value.signature.parameters.elements
    arguments prepared.inputs
  body : LocalApplicationReturnBodyElaborates prepared.inputs.names prepared.inputs.context
    declaration.value.body prepared.core prepared.returnType

def prepareRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option PreparedRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
  let (core, inferredType) ← elaborateLocalApplicationReturnBody? inputs.names inputs.context declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

/-- Preserve faults and genuine exhaustion as present results. Structural
argument evidence does not validate the actual store or referenced locations. -/
def runRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let prepared ← prepareRuntimeApplicationFunction? types owner declaration arguments
  return (prepared.returnType, Core.runStateful fuel
    (Core.State.initial prepared.core (Resolved.LocalScope.values prepared.inputs.environment) store))

end Solcore.Frontend
