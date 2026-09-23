import Solcore.Syntax.Yul

/-! External consumers for recursive inline-Yul statement validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @List.ValidFor
example := @YulReturnClause.ValidFor
example := @YulStmt.ValidFor
example := @YulCase.ValidFor
example := @YulStmt.ValidFor.span_valid
example := @YulCase.ValidFor.span_valid

example (file : SourceFile) (span : SourceSpan)
    (body : List YulStmt)
    (spanValid : span.ValidFor file)
    (bodyValid : List.ValidFor YulStmt.ValidFor file body) :
    YulStmt.ValidFor file { span, value := .block body } :=
  .block spanValid bodyValid

example (file : SourceFile) (span : SourceSpan)
    (scrutinee : YulExpr) (cases : NonemptyList YulCase)
    (defaultBody : Option (List YulStmt))
    (spanValid : span.ValidFor file)
    (scrutineeValid : YulExpr.ValidFor file scrutinee)
    (casesValid : cases.ValidFor YulCase.ValidFor file)
    (defaultValid : ∀ statements ∈ defaultBody,
      ∀ statement ∈ statements, YulStmt.ValidFor file statement) :
    YulStmt.ValidFor file {
      span
      value := .switch scrutinee cases defaultBody
    } :=
  .switch spanValid scrutineeValid casesValid defaultValid

end Tests
