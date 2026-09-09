import Solcore.Frontend.RuntimeFunctionCompilation
import Solcore.Frontend.LocalApplicationReturnBody

/-! Value-free compilation for a separate original application-return entry.
The existing output record is data only; this profile has its own provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeApplicationFunctionCompiles (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : LocalApplicationReturnBodyElaborates compiled.inputs.names compiled.inputs.context
    declaration.value.body compiled.core compiled.returnType

def compileRuntimeApplicationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateLocalApplicationReturnBody? inputs.names inputs.context declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

end Solcore.Frontend
