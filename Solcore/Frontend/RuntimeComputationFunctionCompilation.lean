import Solcore.Frontend.RuntimeFunctionCompilation
import Solcore.Frontend.LocalComputationReturnTree

/-! Value-free compilation of original mixed bodies under the unchanged header
and parameter policy. Reusing an output record does not grant old provenance. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure RuntimeComputationFunctionCompiles (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : LocalComputationReturnTreeElaborates types owner compiled.inputs
    declaration.value.body compiled.core compiled.returnType

def compileRuntimeComputationFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateLocalComputationReturnTree? types owner inputs declaration.value.body
  if inferredType = returnType then return { inputs, core, returnType }
  else none

end Solcore.Frontend
