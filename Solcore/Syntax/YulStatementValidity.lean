import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.YulValidity

/-! Recursive source-validity contracts for canonical inline-Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace YulReturnClause

/-- Every range retained by a Yul return-name clause belongs to one source. -/
def ValidFor (file : SourceFile) (clause : YulReturnClause) : Prop :=
  clause.span.ValidFor file ∧
    clause.value.arrow.ValidFor file ∧
    clause.value.names.ValidFor
      (fun source name => name.span.ValidFor source) file

/-- The outer range of a valid return-name clause is source-valid. -/
theorem ValidFor.span_valid {file : SourceFile} {clause : YulReturnClause}
    (valid : ValidFor file clause) : clause.span.ValidFor file :=
  valid.1

end YulReturnClause

mutual

/-- Every range recursively retained by an inline-Yul statement is valid. -/
inductive YulStmt.ValidFor (file : SourceFile) : YulStmt → Prop where
  | block {span : SourceSpan} {body : List YulStmt}
      (spanValid : span.ValidFor file)
      (bodyValid : ∀ statement ∈ body,
        YulStmt.ValidFor file statement) :
      YulStmt.ValidFor file { span, value := .block body }
  | letDecl {span : SourceSpan} {names : NonemptyList YulIdentifier}
      {initializer : Option YulExpr}
      (spanValid : span.ValidFor file)
      (namesValid : names.ValidFor
        (fun source name => name.span.ValidFor source) file)
      (initializerValid : Option.ValidFor YulExpr.ValidFor file initializer) :
      YulStmt.ValidFor file { span, value := .letDecl names initializer }
  | assign {span : SourceSpan} {names : NonemptyList YulIdentifier}
      {value : YulExpr}
      (spanValid : span.ValidFor file)
      (namesValid : names.ValidFor
        (fun source name => name.span.ValidFor source) file)
      (valueValid : YulExpr.ValidFor file value) :
      YulStmt.ValidFor file { span, value := .assign names value }
  | expression {span : SourceSpan} {expression : YulExpr}
      (spanValid : span.ValidFor file)
      (expressionValid : YulExpr.ValidFor file expression) :
      YulStmt.ValidFor file { span, value := .expression expression }
  | ifThen {span : SourceSpan} {condition : YulExpr} {body : List YulStmt}
      (spanValid : span.ValidFor file)
      (conditionValid : YulExpr.ValidFor file condition)
      (bodyValid : ∀ statement ∈ body,
        YulStmt.ValidFor file statement) :
      YulStmt.ValidFor file { span, value := .ifThen condition body }
  | forLoop {span : SourceSpan} {initializer : List YulStmt}
      {condition : YulExpr} {post body : List YulStmt}
      (spanValid : span.ValidFor file)
      (initializerValid : ∀ statement ∈ initializer,
        YulStmt.ValidFor file statement)
      (conditionValid : YulExpr.ValidFor file condition)
      (postValid : ∀ statement ∈ post,
        YulStmt.ValidFor file statement)
      (bodyValid : ∀ statement ∈ body,
        YulStmt.ValidFor file statement) :
      YulStmt.ValidFor file {
        span
        value := .forLoop initializer condition post body
      }
  | switch {span : SourceSpan} {scrutinee : YulExpr}
      {cases : NonemptyList YulCase} {defaultBody : Option (List YulStmt)}
      (spanValid : span.ValidFor file)
      (scrutineeValid : YulExpr.ValidFor file scrutinee)
      (casesValid : ∀ case ∈ cases.toList,
        YulCase.ValidFor file case)
      (defaultValid : ∀ statements ∈ defaultBody,
        ∀ statement ∈ statements, YulStmt.ValidFor file statement) :
      YulStmt.ValidFor file {
        span
        value := .switch scrutinee cases defaultBody
      }
  | functionDef {span : SourceSpan} {name : YulIdentifier}
      {parameters : DelimitedList YulIdentifier}
      {returns : Option YulReturnClause} {body : List YulStmt}
      (spanValid : span.ValidFor file)
      (nameValid : name.span.ValidFor file)
      (parametersValid : parameters.ValidFor
        (fun source parameter => parameter.span.ValidFor source) file)
      (returnsValid : Option.ValidFor
        YulReturnClause.ValidFor file returns)
      (bodyValid : ∀ statement ∈ body,
        YulStmt.ValidFor file statement) :
      YulStmt.ValidFor file {
        span
        value := .functionDef name parameters returns body
      }
  | leave {span : SourceSpan} (spanValid : span.ValidFor file) :
      YulStmt.ValidFor file { span, value := .leave }
  | break {span : SourceSpan} (spanValid : span.ValidFor file) :
      YulStmt.ValidFor file { span, value := .break }
  | continue {span : SourceSpan} (spanValid : span.ValidFor file) :
      YulStmt.ValidFor file { span, value := .continue }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      YulStmt.ValidFor file { span, value := .error }

/-- Every range recursively retained by an inline-Yul switch arm is valid. -/
inductive YulCase.ValidFor (file : SourceFile) : YulCase → Prop where
  | arm {span : SourceSpan} {literal : YulLiteral} {body : List YulStmt}
      (spanValid : span.ValidFor file)
      (literalValid : literal.span.ValidFor file)
      (bodyValid : ∀ statement ∈ body,
        YulStmt.ValidFor file statement) :
      YulCase.ValidFor file { span, value := .arm literal body }

end

namespace YulStmt.ValidFor

/-- The outer range retained by every valid Yul statement is source-valid. -/
theorem span_valid {file : SourceFile} {statement : YulStmt}
    (valid : YulStmt.ValidFor file statement) :
    statement.span.ValidFor file := by
  cases valid <;> assumption

end YulStmt.ValidFor

namespace YulCase.ValidFor

/-- The outer range retained by every valid Yul case is source-valid. -/
theorem span_valid {file : SourceFile} {case : YulCase}
    (valid : YulCase.ValidFor file case) : case.span.ValidFor file := by
  cases valid
  assumption

end YulCase.ValidFor

end Solcore.Syntax
