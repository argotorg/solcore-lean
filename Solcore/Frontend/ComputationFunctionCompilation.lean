import Solcore.Frontend.RuntimeFunctionCompilation
import Solcore.Frontend.ComputationReturnTree

set_option autoImplicit false

namespace Solcore.Frontend

/-! Value-free compilation of original mixed bodies under the unchanged header
and parameter policy. Reusing an output record does not grant old provenance. -/

structure ComputationFunctionCompiles (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : ComputationReturnTreeElaborates ChildElab types owner compiled.inputs
    declaration.value.body compiled.core compiled.returnType

def compileComputationFunction? (checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty))
    (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateComputationReturnTree? checkChild types owner inputs declaration.value.body
  if inferredType = returnType then return { inputs, core, returnType }
  else none

end Solcore.Frontend
