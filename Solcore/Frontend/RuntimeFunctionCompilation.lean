import Solcore.Frontend.RuntimeFunctionHeader
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.TerminalReturnTreeProperties

/-! Compile one restricted explicit entry without supplying argument values.
The retained Core is open in the parameter context, not a source function value. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Data only: a hand-built record does not establish compilation or typing. -/
structure CompiledRuntimeFunction where
  inputs : LocalTypeInputs
  core : Core.Expr
  returnType : Core.Ty

/-- Independent whole-entry evidence fixes the exact elaborated Core and
declared return type without assuming any runtime argument inhabitants. -/
structure RuntimeFunctionCompiles (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction) : Prop where
  header : RuntimeFunctionHeader types declaration.value.signature compiled.returnType
  parameters : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements
    compiled.inputs
  body : TerminalReturnTreeElaborates compiled.inputs.names compiled.inputs.context
    declaration.value.body compiled.core compiled.returnType

/-- Keep the existing header policy and check the whole recursive tree. Retain
the actual Core only when its inferred type agrees with the return contract. -/
def compileRuntimeFunction? (types : TypeNameTable) (owner : Resolved.DeclarationId)
    (declaration : Syntax.FunctionDecl) : Option CompiledRuntimeFunction := do
  let returnType ← interpretRuntimeFunctionHeader? types declaration.value.signature
  let inputs ← declareRuntimeParameters? types owner declaration.value.signature.parameters.elements
  let (core, inferredType) ← elaborateTerminalReturnTree? inputs.names inputs.context declaration.value.body
  if inferredType = returnType then
    return { inputs, core, returnType }
  else none

end Solcore.Frontend
