import Solcore.Syntax.TypeValidity

/-! Source-validity contracts for canonical function and lambda parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace FunctionParameter

/-- Every range retained by a named-function parameter belongs to one source. -/
inductive ValidFor (file : SourceFile) : FunctionParameter → Prop where
  | typed {span : SourceSpan} {comptime : Option SourceSpan}
      {name : Identifier} {type : TypeExpr}
      (spanValid : span.ValidFor file)
      (comptimeValid : ∀ marker ∈ comptime, marker.ValidFor file)
      (nameValid : name.span.ValidFor file)
      (typeValid : TypeExpr.ValidFor file type) :
      ValidFor file { span, value := .typed comptime name type }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor file { span, value := .error }

/-- A valid function parameter has a valid outer range. -/
theorem ValidFor.span_valid {file : SourceFile} {parameter : FunctionParameter}
    (valid : ValidFor file parameter) : parameter.span.ValidFor file := by
  cases valid <;> assumption

end FunctionParameter

namespace LambdaParameter

/-- Every range retained by a lambda parameter belongs to one source. -/
inductive ValidFor (file : SourceFile) : LambdaParameter → Prop where
  | inferred {span : SourceSpan} {name : Identifier}
      (spanValid : span.ValidFor file)
      (nameValid : name.span.ValidFor file) :
      ValidFor file { span, value := .inferred name }
  | typed {span : SourceSpan} {comptime : Option SourceSpan}
      {name : Identifier} {type : TypeExpr}
      (spanValid : span.ValidFor file)
      (comptimeValid : ∀ marker ∈ comptime, marker.ValidFor file)
      (nameValid : name.span.ValidFor file)
      (typeValid : TypeExpr.ValidFor file type) :
      ValidFor file { span, value := .typed comptime name type }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor file { span, value := .error }

/-- A valid lambda parameter has a valid outer range. -/
theorem ValidFor.span_valid {file : SourceFile} {parameter : LambdaParameter}
    (valid : ValidFor file parameter) : parameter.span.ValidFor file := by
  cases valid <;> assumption

end LambdaParameter

end Solcore.Syntax
