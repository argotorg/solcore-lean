import Solcore.Syntax.ExpressionValidity

/-! External consumers for recursive canonical expression validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @FunctionParameter.ValidFor
example := @LambdaParameter.ValidFor
example := @Block.ValidFor
example := @Expr.ValidFor
example := @Expr.ValidFor.span_valid

example (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (span : SourceSpan) (name : Identifier)
    (spanValid : span.ValidFor file) (nameValid : name.span.ValidFor file) :
    Expr.ValidFor statementValid file {
      span
      value := .identifier name
    } :=
  .identifier spanValid nameValid

example (statementValid : SourceFile → Statement → Prop)
    (file : SourceFile) (span : SourceSpan)
    (callee : Expr) (arguments : DelimitedList Expr)
    (spanValid : span.ValidFor file)
    (calleeValid : Expr.ValidFor statementValid file callee)
    (argumentsSpanValid : arguments.span.ValidFor file)
    (argumentsValid : ∀ argument ∈ arguments.elements,
      Expr.ValidFor statementValid file argument) :
    Expr.ValidFor statementValid file {
      span
      value := .call callee arguments
    } :=
  .call spanValid calleeValid argumentsSpanValid argumentsValid

end Tests
