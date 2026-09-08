import Solcore.Frontend.RuntimeParameterDeclarationReferenceProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

/-! Whole-entry positional selectors compile without constructing argument
values. Guard and arm positions may coincide when their annotation types agree. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {inputs : LocalTypeInputs}
  {conditionIndex thenIndex elseIndex : Nat}
  {conditionParameterSpan thenParameterSpan elseParameterSpan : Syntax.SourceSpan}
  {conditionName thenName elseName : Syntax.Identifier}
  {conditionAnnotation thenAnnotation elseAnnotation : Syntax.TypeExpr} {type : Core.Ty}
  {blockSpan ifSpan conditionSpan conditionNameSpan : Syntax.SourceSpan}
  {thenBlockSpan thenReturnSpan thenSpan thenNameSpan : Syntax.SourceSpan}
  {elseBlockSpan elseReturnSpan elseSpan elseNameSpan : Syntax.SourceSpan}

private theorem conditional_parameter_body_elaborates
    (declared : RuntimeParametersDeclare types owner
      declaration.value.signature.parameters.elements inputs)
    (conditionAt : declaration.value.signature.parameters.elements[conditionIndex]? =
      some ⟨conditionParameterSpan, .typed none conditionName conditionAnnotation⟩)
    (thenAt : declaration.value.signature.parameters.elements[thenIndex]? =
      some ⟨thenParameterSpan, .typed none thenName thenAnnotation⟩)
    (elseAt : declaration.value.signature.parameters.elements[elseIndex]? =
      some ⟨elseParameterSpan, .typed none elseName elseAnnotation⟩)
    (conditionMeaning : TypeNameDenotes types conditionAnnotation .bool)
    (thenMeaning : TypeNameDenotes types thenAnnotation type)
    (elseMeaning : TypeNameDenotes types elseAnnotation type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨ifSpan, .ifThen
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionName.value⟩⟩
        ⟨thenBlockSpan, [⟨thenReturnSpan,
          .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenName.value⟩⟩)⟩]⟩
        (some ⟨elseBlockSpan, [⟨elseReturnSpan,
          .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseName.value⟩⟩)⟩]⟩)⟩]⟩) :
    TerminalReturnTreeElaborates inputs.names inputs.context declaration.value.body
      (.ifE (.var (declaration.value.signature.parameters.elements.length - 1 - conditionIndex))
        (.var (declaration.value.signature.parameters.elements.length - 1 - thenIndex))
        (.var (declaration.value.signature.parameters.elements.length - 1 - elseIndex))) type := by
  rw [bodyShape]
  obtain ⟨_, _, actualMeaning, _, named, found, indexed⟩ := declared.position conditionAt
  cases actualMeaning.type_unique conditionMeaning
  exact .conditional (.identifier named) (.var indexed) (.var found)
    (.single (declared.reference_return_elaborates_at thenAt thenMeaning
      thenBlockSpan thenReturnSpan thenSpan thenNameSpan))
    (.single (declared.reference_return_elaborates_at elseAt elseMeaning
      elseBlockSpan elseReturnSpan elseSpan elseNameSpan))

/-- All parameters and the whole header remain prerequisites, even when both
arms select the same parameter or the Bool condition is also returned. -/
theorem runtimeFunction_conditional_parameters_compiles
    (declared : RuntimeParametersDeclare types owner
      declaration.value.signature.parameters.elements inputs)
    (conditionAt : declaration.value.signature.parameters.elements[conditionIndex]? =
      some ⟨conditionParameterSpan, .typed none conditionName conditionAnnotation⟩)
    (thenAt : declaration.value.signature.parameters.elements[thenIndex]? =
      some ⟨thenParameterSpan, .typed none thenName thenAnnotation⟩)
    (elseAt : declaration.value.signature.parameters.elements[elseIndex]? =
      some ⟨elseParameterSpan, .typed none elseName elseAnnotation⟩)
    (conditionMeaning : TypeNameDenotes types conditionAnnotation .bool)
    (thenMeaning : TypeNameDenotes types thenAnnotation type)
    (elseMeaning : TypeNameDenotes types elseAnnotation type)
    (header : RuntimeFunctionHeader types declaration.value.signature type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨ifSpan, .ifThen
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionName.value⟩⟩
        ⟨thenBlockSpan, [⟨thenReturnSpan,
          .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenName.value⟩⟩)⟩]⟩
        (some ⟨elseBlockSpan, [⟨elseReturnSpan,
          .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseName.value⟩⟩)⟩]⟩)⟩]⟩) :
    RuntimeFunctionCompiles types owner declaration
      { inputs, core := .ifE
          (.var (declaration.value.signature.parameters.elements.length - 1 - conditionIndex))
          (.var (declaration.value.signature.parameters.elements.length - 1 - thenIndex))
          (.var (declaration.value.signature.parameters.elements.length - 1 - elseIndex)),
        returnType := type } :=
  ⟨header, declared, conditional_parameter_body_elaborates declared conditionAt thenAt elseAt
    conditionMeaning thenMeaning elseMeaning bodyShape⟩

theorem compileRuntimeFunction?_conditional_parameters
    (declared : RuntimeParametersDeclare types owner
      declaration.value.signature.parameters.elements inputs)
    (conditionAt : declaration.value.signature.parameters.elements[conditionIndex]? =
      some ⟨conditionParameterSpan, .typed none conditionName conditionAnnotation⟩)
    (thenAt : declaration.value.signature.parameters.elements[thenIndex]? =
      some ⟨thenParameterSpan, .typed none thenName thenAnnotation⟩)
    (elseAt : declaration.value.signature.parameters.elements[elseIndex]? =
      some ⟨elseParameterSpan, .typed none elseName elseAnnotation⟩)
    (conditionMeaning : TypeNameDenotes types conditionAnnotation .bool)
    (thenMeaning : TypeNameDenotes types thenAnnotation type)
    (elseMeaning : TypeNameDenotes types elseAnnotation type)
    (header : RuntimeFunctionHeader types declaration.value.signature type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨ifSpan, .ifThen
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionName.value⟩⟩
        ⟨thenBlockSpan, [⟨thenReturnSpan,
          .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenName.value⟩⟩)⟩]⟩
        (some ⟨elseBlockSpan, [⟨elseReturnSpan,
          .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseName.value⟩⟩)⟩]⟩)⟩]⟩) :
    compileRuntimeFunction? types owner declaration = some
      { inputs, core := .ifE
          (.var (declaration.value.signature.parameters.elements.length - 1 - conditionIndex))
          (.var (declaration.value.signature.parameters.elements.length - 1 - thenIndex))
          (.var (declaration.value.signature.parameters.elements.length - 1 - elseIndex)),
        returnType := type } :=
  (runtimeFunction_conditional_parameters_compiles declared conditionAt thenAt elseAt
    conditionMeaning thenMeaning elseMeaning header bodyShape).complete

/-- Existing provenance supplies the full declaration evidence. Exact body
uniqueness distinguishes the positional selector from merely equally typed Core. -/
theorem RuntimeFunctionCompiles.conditional_parameters_core
    {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled)
    (conditionAt : declaration.value.signature.parameters.elements[conditionIndex]? =
      some ⟨conditionParameterSpan, .typed none conditionName conditionAnnotation⟩)
    (thenAt : declaration.value.signature.parameters.elements[thenIndex]? =
      some ⟨thenParameterSpan, .typed none thenName thenAnnotation⟩)
    (elseAt : declaration.value.signature.parameters.elements[elseIndex]? =
      some ⟨elseParameterSpan, .typed none elseName elseAnnotation⟩)
    (conditionMeaning : TypeNameDenotes types conditionAnnotation .bool)
    (thenMeaning : TypeNameDenotes types thenAnnotation type)
    (elseMeaning : TypeNameDenotes types elseAnnotation type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨ifSpan, .ifThen
        ⟨conditionSpan, .identifier ⟨conditionNameSpan, conditionName.value⟩⟩
        ⟨thenBlockSpan, [⟨thenReturnSpan,
          .returnStmt (some ⟨thenSpan, .identifier ⟨thenNameSpan, thenName.value⟩⟩)⟩]⟩
        (some ⟨elseBlockSpan, [⟨elseReturnSpan,
          .returnStmt (some ⟨elseSpan, .identifier ⟨elseNameSpan, elseName.value⟩⟩)⟩]⟩)⟩]⟩) :
    compiled.core = .ifE
        (.var (declaration.value.signature.parameters.elements.length - 1 - conditionIndex))
        (.var (declaration.value.signature.parameters.elements.length - 1 - thenIndex))
        (.var (declaration.value.signature.parameters.elements.length - 1 - elseIndex)) ∧
      compiled.returnType = type :=
  compilation.body.result_unique
    (conditional_parameter_body_elaborates compilation.parameters conditionAt thenAt elseAt
      conditionMeaning thenMeaning elseMeaning bodyShape)

end Solcore.Frontend
