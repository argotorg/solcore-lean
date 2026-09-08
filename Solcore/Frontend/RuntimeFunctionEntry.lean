import Solcore.Frontend.RuntimeFunctionHeader
import Solcore.Frontend.RuntimeParametersProperties
import Solcore.Frontend.LocalInputsTypeErasure
import Solcore.Frontend.TypedLetReturnTreeProperties

/-! An explicitly supplied declaration, owner, type table, and typed arguments
form one restricted external entry. This does not resolve or invoke source calls. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Data only: arbitrary hand-built records receive no safety guarantee. -/
structure PreparedRuntimeFunction where
  inputs : LocalInputs
  core : Core.Expr
  returnType : Core.Ty

/-- Exact preparation provenance, independent of executable preparation.
The body evidence fixes the actual Core, not merely a Core of the same type. -/
structure RuntimeFunctionPrepares (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (prepared : PreparedRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature prepared.returnType
  parameters : RuntimeParametersBind types owner declaration.value.signature.parameters.elements
    arguments prepared.inputs
  body : TypedLetReturnTreeElaborates types owner prepared.inputs.toTypeInputs
    declaration.value.body prepared.core prepared.returnType

/-- The whole entry contract, distinct from checking the body by itself. -/
def RuntimeFunctionHasType (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (returnType : Core.Ty) : Prop :=
  ∃ inputs, RuntimeFunctionHeader types declaration.value.signature returnType ∧
    RuntimeParametersBind types owner declaration.value.signature.parameters.elements arguments inputs ∧
    TypedLetReturnTreeHasType types owner inputs.toTypeInputs declaration.value.body returnType

/-- Retain the body checker's returned Core only when it matches the explicit
return contract. Unknown or unsupported components have no fallback meaning. -/
def prepareRuntimeFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument) :
    Option PreparedRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← bindRuntimeParameters? types owner declaration.value.signature.parameters.elements arguments
  let (core, inferredType) ← elaborateTypedLetReturnTree? types owner inputs.toTypeInputs declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

/-- Execute exactly the prepared Core and values. Preparation is not part of
the Core fuel count, and present exhaustion remains a present result. -/
def runRuntimeFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (store : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) := do
  let prepared ← prepareRuntimeFunction? types owner declaration arguments
  return (prepared.returnType, Core.runStateful fuel
    (Core.State.initial prepared.core (Resolved.LocalScope.values prepared.inputs.environment) store))

end Solcore.Frontend
