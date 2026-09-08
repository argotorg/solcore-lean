import Solcore.Frontend.RuntimeParameterDeclarationReferenceProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

/-! Whole-entry compilation of a source-positioned parameter return needs no
runtime arguments. Exact body evidence, not type agreement, fixes its Core. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {inputs : LocalTypeInputs} {type : Core.Ty}
  {index : Nat} {parameterSpan : Syntax.SourceSpan} {name : Syntax.Identifier}
  {annotation : Syntax.TypeExpr} {blockSpan returnSpan span nameSpan : Syntax.SourceSpan}

private theorem parameter_body_elaboration
    (declared : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    TypedLetReturnTreeElaborates types owner inputs declaration.value.body
      (.var (declaration.value.signature.parameters.elements.length - 1 - index)) type := by
  rw [bodyShape]
  exact .single
    (declared.reference_return_elaborates_at parameterAt meaning blockSpan returnSpan span nameSpan)

/-- Header and complete parameter declaration remain necessary even when the
body returns only one parameter. Its source lookup supplies the positional bound. -/
theorem runtimeFunction_parameter_compiles
    (declared : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (header : RuntimeFunctionHeader types declaration.value.signature type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    RuntimeFunctionCompiles types owner declaration
      { inputs, core := .var (declaration.value.signature.parameters.elements.length - 1 - index),
        returnType := type } :=
  ⟨header, declared, parameter_body_elaboration declared parameterAt meaning bodyShape⟩

theorem compileRuntimeFunction?_parameter
    (declared : RuntimeParametersDeclare types owner declaration.value.signature.parameters.elements inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (header : RuntimeFunctionHeader types declaration.value.signature type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    compileRuntimeFunction? types owner declaration = some
      { inputs, core := .var (declaration.value.signature.parameters.elements.length - 1 - index),
        returnType := type } :=
  (runtimeFunction_parameter_compiles declared parameterAt meaning header bodyShape).complete

/-- Existing provenance already supplies the whole header and parameter list.
An equally typed alternative Core is not another result for this source body. -/
theorem RuntimeFunctionCompiles.parameter_return_core {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (meaning : TypeNameDenotes types annotation type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    compiled.core = .var (declaration.value.signature.parameters.elements.length - 1 - index) ∧
      compiled.returnType = type :=
  compilation.body.result_unique (parameter_body_elaboration compilation.parameters parameterAt meaning bodyShape)

end Solcore.Frontend
