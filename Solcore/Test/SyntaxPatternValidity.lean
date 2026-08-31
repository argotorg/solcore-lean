import Solcore.Syntax.PatternValidity

/-! External consumers for recursive canonical pattern validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @Pattern.ValidFor
example := @Pattern.ValidFor.span_valid

example (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (span marker : SourceSpan)
    (spanValid : span.ValidFor file) (markerValid : marker.ValidFor file) :
    Pattern.ValidFor expressionValid file {
      span
      value := .wildcard marker
    } :=
  .wildcard spanValid markerValid

example (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) (span : SourceSpan)
    (elements : DelimitedList Pattern)
    (spanValid : span.ValidFor file)
    (elementsSpanValid : elements.span.ValidFor file)
    (elementsValid : ∀ element ∈ elements.elements,
      Pattern.ValidFor expressionValid file element) :
    Pattern.ValidFor expressionValid file {
      span
      value := .tuple elements
    } :=
  .tuple spanValid elementsSpanValid elementsValid

end Tests
