import Solcore.Syntax.NameValidity
import Solcore.Syntax.Type

/-! Source-validity contract for recursive canonical type expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace TypeExpr

/--
A recursive type expression is valid when its outer range and every range
retained by its payload belong to the same source file.
-/
inductive ValidFor (file : SourceFile) : TypeExpr → Prop where
  | namedWithoutArguments {span : SourceSpan} {name : QualifiedName}
      (spanValid : span.ValidFor file)
      (nameValid : QualifiedName.ValidFor file name) :
      ValidFor file { span, value := .named name none }
  | namedWithArguments {span : SourceSpan} {name : QualifiedName}
      {arguments : NonemptyDelimitedList TypeExpr}
      (spanValid : span.ValidFor file)
      (nameValid : QualifiedName.ValidFor file name)
      (argumentsSpanValid : arguments.span.ValidFor file)
      (argumentsValid : ∀ argument ∈ arguments.elements.toList,
        ValidFor file argument) :
      ValidFor file { span, value := .named name (some arguments) }
  | mapping {span keyword argumentsSpan : SourceSpan}
      {key value : TypeExpr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (argumentsSpanValid : argumentsSpan.ValidFor file)
      (keyValid : ValidFor file key)
      (valueValid : ValidFor file value) :
      ValidFor file {
        span
        value := .mapping keyword argumentsSpan key value
      }
  | proxy {span marker : SourceSpan} {inner : TypeExpr}
      (spanValid : span.ValidFor file)
      (markerValid : marker.ValidFor file)
      (innerValid : ValidFor file inner) :
      ValidFor file { span, value := .proxy marker inner }
  | functionWithoutReturns {span keyword : SourceSpan}
      {parameters : DelimitedList TypeExpr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (parametersSpanValid : parameters.span.ValidFor file)
      (parametersValid : ∀ parameter ∈ parameters.elements,
        ValidFor file parameter) :
      ValidFor file {
        span
        value := .function keyword parameters none
      }
  | functionWithReturns {span keyword : SourceSpan}
      {parameters returns : DelimitedList TypeExpr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (parametersSpanValid : parameters.span.ValidFor file)
      (parametersValid : ∀ parameter ∈ parameters.elements,
        ValidFor file parameter)
      (returnsSpanValid : returns.span.ValidFor file)
      (returnsValid : ∀ result ∈ returns.elements,
        ValidFor file result) :
      ValidFor file {
        span
        value := .function keyword parameters (some returns)
      }
  | comptime {span keyword argumentsSpan : SourceSpan}
      {inner : TypeExpr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (argumentsSpanValid : argumentsSpan.ValidFor file)
      (innerValid : ValidFor file inner) :
      ValidFor file {
        span
        value := .comptime keyword argumentsSpan inner
      }
  | tuple {span : SourceSpan} {elements : List TypeExpr}
      (spanValid : span.ValidFor file)
      (elementsValid : ∀ element ∈ elements, ValidFor file element) :
      ValidFor file { span, value := .tuple elements }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor file { span, value := .error }

/-- The outer range retained by every valid type expression is source-valid. -/
theorem ValidFor.span_valid {file : SourceFile} {value : TypeExpr}
    (valid : ValidFor file value) : value.span.ValidFor file := by
  cases valid <;> assumption

end TypeExpr

end Solcore.Syntax
