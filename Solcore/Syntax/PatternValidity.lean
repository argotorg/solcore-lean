import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.Term

/-! Recursive source-validity contract for canonical Core patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.Pattern

/--
Every range recursively retained by a pattern belongs to one source.  The
contract for embedded comptime expressions is supplied by the expression
layer, so pattern provenance can be established independently.
-/
inductive ValidFor (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : Pattern → Prop where
  | wildcard {span marker : SourceSpan}
      (spanValid : span.ValidFor file)
      (markerValid : marker.ValidFor file) :
      ValidFor expressionValid file { span, value := .wildcard marker }
  | literal {span : SourceSpan} {literal : CoreLiteral}
      (spanValid : span.ValidFor file)
      (literalValid : literal.span.ValidFor file) :
      ValidFor expressionValid file { span, value := .literal literal }
  | binder {span : SourceSpan} {name : Identifier}
      (spanValid : span.ValidFor file)
      (nameValid : name.span.ValidFor file) :
      ValidFor expressionValid file { span, value := .binder name }
  | constructor {span : SourceSpan} {leadingDot : Option SourceSpan}
      {qualifiers : List Identifier} {name : Identifier}
      {arguments : Option (NonemptyDelimitedList Pattern)}
      (spanValid : span.ValidFor file)
      (leadingDotValid : ∀ marker ∈ leadingDot, marker.ValidFor file)
      (qualifiersValid : ∀ qualifier ∈ qualifiers,
        qualifier.span.ValidFor file)
      (nameValid : name.span.ValidFor file)
      (argumentsSpanValid : ∀ values ∈ arguments,
        values.span.ValidFor file)
      (argumentsValid : ∀ values ∈ arguments,
        ∀ pattern ∈ values.elements.toList,
          ValidFor expressionValid file pattern) :
      ValidFor expressionValid file {
        span
        value := .constructor leadingDot qualifiers name arguments
      }
  | comptime {span keyword : SourceSpan} {expression : Expr}
      (spanValid : span.ValidFor file)
      (keywordValid : keyword.ValidFor file)
      (expressionIsValid : expressionValid file expression) :
      ValidFor expressionValid file {
        span
        value := .comptime keyword expression
      }
  | group {span : SourceSpan} {inner : Pattern}
      (spanValid : span.ValidFor file)
      (innerValid : ValidFor expressionValid file inner) :
      ValidFor expressionValid file { span, value := .group inner }
  | tuple {span : SourceSpan} {elements : DelimitedList Pattern}
      (spanValid : span.ValidFor file)
      (elementsSpanValid : elements.span.ValidFor file)
      (elementsValid : ∀ element ∈ elements.elements,
        ValidFor expressionValid file element) :
      ValidFor expressionValid file { span, value := .tuple elements }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      ValidFor expressionValid file { span, value := .error }

/-- The outer range retained by every valid pattern is source-valid. -/
theorem ValidFor.span_valid {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {pattern : Pattern}
    (valid : ValidFor expressionValid file pattern) :
    pattern.span.ValidFor file := by
  cases valid <;> assumption

end Solcore.Syntax.Pattern
