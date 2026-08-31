import Solcore.Syntax.StatementValidity

/-! External consumers for recursive canonical statement validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @ForItem.ValidFor
example := @Statement.ValidFor
example := @MatchCase.ValidFor
example := @MatchArms.ValidFor
example := @Statement.ValidFor.span_valid

example (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) (span : SourceSpan) (value : Option Expr)
    (spanValid : span.ValidFor file)
    (valueValid : ∀ expression ∈ value, expressionValid file expression) :
    Statement.ValidFor expressionValid patternValid yulValid file {
      span
      value := .returnStmt value
    } :=
  .returnStmt spanValid valueValid

example (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) (span : SourceSpan) (body : List Statement)
    (spanValid : span.ValidFor file)
    (bodyValid : ∀ statement ∈ body,
      Statement.ValidFor expressionValid patternValid yulValid file statement) :
    Statement.ValidFor expressionValid patternValid yulValid file {
      span
      value := .block body
    } :=
  .block spanValid bodyValid

end Tests
