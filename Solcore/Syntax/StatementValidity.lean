import Solcore.Syntax.ExpressionValidity
import Solcore.Syntax.PatternValidity
import Solcore.Syntax.YulStatementValidity

/-! Recursive source-validity contracts for canonical Core statements. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace ForItem

/-- Every range retained by one canonical `for` header item is valid. -/
inductive ValidFor (expressionValid : SourceFile → Expr → Prop)
    (file : SourceFile) : ForItem → Prop where
  | letDecl {span : SourceSpan} {name : Identifier}
      {type : Option TypeExpr} {initializer : Option Expr}
      (spanValid : span.ValidFor file) (nameValid : name.span.ValidFor file)
      (typeValid : ∀ value ∈ type, TypeExpr.ValidFor file value)
      (initializerValid : ∀ value ∈ initializer, expressionValid file value) :
      ValidFor expressionValid file {
        span
        value := .letDecl name type initializer
      }
  | expression {span : SourceSpan} {expression : Expr}
      (spanValid : span.ValidFor file)
      (expressionIsValid : expressionValid file expression) :
      ValidFor expressionValid file { span, value := .expression expression }
  | assignValue {span : SourceSpan} {target value : Expr}
      {operator : Located ValueAssignOp}
      (spanValid : span.ValidFor file)
      (targetValid : expressionValid file target)
      (operatorValid : operator.span.ValidFor file)
      (valueValid : expressionValid file value) :
      ValidFor expressionValid file {
        span
        value := .assignValue target operator value
      }
  | assignBitNot {span operator : SourceSpan} {target : Expr}
      (spanValid : span.ValidFor file)
      (targetValid : expressionValid file target)
      (operatorValid : operator.ValidFor file) :
      ValidFor expressionValid file {
        span
        value := .assignBitNot target operator
      }

/-- A valid `for` item has a valid outer range. -/
theorem ValidFor.span_valid {expressionValid : SourceFile → Expr → Prop}
    {file : SourceFile} {item : ForItem}
    (valid : ValidFor expressionValid file item) : item.span.ValidFor file := by
  cases valid <;> assumption

end ForItem

mutual

/-- Every range recursively retained by a Core statement is valid. -/
inductive Statement.ValidFor
    (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) : Statement → Prop where
  | letDecl {span : SourceSpan} {name : Identifier}
      {type : Option TypeExpr} {initializer : Option Expr}
      (spanValid : span.ValidFor file) (nameValid : name.span.ValidFor file)
      (typeValid : ∀ value ∈ type, TypeExpr.ValidFor file value)
      (initializerValid : ∀ value ∈ initializer, expressionValid file value) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .letDecl name type initializer
      }
  | returnStmt {span : SourceSpan} {value : Option Expr}
      (spanValid : span.ValidFor file)
      (valueValid : ∀ expression ∈ value, expressionValid file expression) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .returnStmt value
      }
  | expression {span : SourceSpan} {expression : Expr}
      {trailingSemicolon : Bool}
      (spanValid : span.ValidFor file)
      (expressionIsValid : expressionValid file expression) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .expression expression trailingSemicolon
      }
  | assignValue {span : SourceSpan} {target value : Expr}
      {operator : Located ValueAssignOp}
      (spanValid : span.ValidFor file)
      (targetValid : expressionValid file target)
      (operatorValid : operator.span.ValidFor file)
      (valueValid : expressionValid file value) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .assignValue target operator value
      }
  | assignBitNot {span operator : SourceSpan} {target : Expr}
      (spanValid : span.ValidFor file)
      (targetValid : expressionValid file target)
      (operatorValid : operator.ValidFor file) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .assignBitNot target operator
      }
  | matchWith {span : SourceSpan}
      {scrutinees : NonemptyDelimitedList Expr} {arms : MatchArms}
      (spanValid : span.ValidFor file)
      (scrutineesSpanValid : scrutinees.span.ValidFor file)
      (scrutineesValid : ∀ expression ∈ scrutinees.elements.toList,
        expressionValid file expression)
      (armsValid : MatchArms.ValidFor expressionValid patternValid
        yulValid file arms) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .matchWith scrutinees arms
      }
  | forLoop {span headerSpan : SourceSpan}
      {initializer post : List ForItem} {condition : Expr} {body : Block}
      (spanValid : span.ValidFor file)
      (headerValid : headerSpan.ValidFor file)
      (initializerValid : ∀ item ∈ initializer,
        ForItem.ValidFor expressionValid file item)
      (conditionValid : expressionValid file condition)
      (postValid : ∀ item ∈ post,
        ForItem.ValidFor expressionValid file item)
      (bodySpanValid : body.span.ValidFor file)
      (bodyValid : ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .forLoop headerSpan initializer condition post body
      }
  | whileLoop {span : SourceSpan} {condition : Expr} {body : Block}
      (spanValid : span.ValidFor file)
      (conditionValid : expressionValid file condition)
      (bodySpanValid : body.span.ValidFor file)
      (bodyValid : ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .whileLoop condition body
      }
  | ifThen {span : SourceSpan} {condition : Expr} {thenBody : Block}
      {elseBody : Option Block}
      (spanValid : span.ValidFor file)
      (conditionValid : expressionValid file condition)
      (thenSpanValid : thenBody.span.ValidFor file)
      (thenValid : ∀ statement ∈ thenBody.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement)
      (elseSpanValid : ∀ body ∈ elseBody, body.span.ValidFor file)
      (elseValid : ∀ body ∈ elseBody, ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .ifThen condition thenBody elseBody
      }
  | block {span : SourceSpan} {body : List Statement}
      (spanValid : span.ValidFor file)
      (bodyValid : ∀ statement ∈ body,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .block body
      }
  | assembly {span : SourceSpan} {body : List YulStmt}
      (spanValid : span.ValidFor file)
      (bodyValid : ∀ statement ∈ body, yulValid file statement) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .assembly body
      }
  | breakStmt {span : SourceSpan} (spanValid : span.ValidFor file) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .breakStmt
      }
  | continueStmt {span : SourceSpan} (spanValid : span.ValidFor file) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .continueStmt
      }
  | error {span : SourceSpan} (spanValid : span.ValidFor file) :
      Statement.ValidFor expressionValid patternValid yulValid file {
        span
        value := .error
      }

/-- Every range retained by a non-default match arm is valid. -/
inductive MatchCase.ValidFor
    (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) : MatchCase → Prop where
  | arm {span : SourceSpan} {pattern : Pattern} {body : Block}
      (spanValid : span.ValidFor file)
      (patternIsValid : patternValid file pattern)
      (bodySpanValid : body.span.ValidFor file)
      (bodyValid : ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      MatchCase.ValidFor expressionValid patternValid yulValid file {
        span
        value := { pattern, body }
      }

/-- Every range retained by a complete match-arm collection is valid. -/
inductive MatchArms.ValidFor
    (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) : MatchArms → Prop where
  | arms {span : SourceSpan} {cases : List MatchCase}
      {defaultBody : Option Block}
      (spanValid : span.ValidFor file)
      (casesValid : ∀ case ∈ cases,
        MatchCase.ValidFor expressionValid patternValid yulValid file case)
      (defaultSpanValid : ∀ body ∈ defaultBody, body.span.ValidFor file)
      (defaultValid : ∀ body ∈ defaultBody, ∀ statement ∈ body.value,
        Statement.ValidFor expressionValid patternValid yulValid file statement) :
      MatchArms.ValidFor expressionValid patternValid yulValid file {
        span
        value := { cases, defaultBody }
      }

end

namespace Statement.ValidFor

/-- A valid statement has a valid outer range. -/
theorem span_valid {expressionValid : SourceFile → Expr → Prop}
    {patternValid : SourceFile → Pattern → Prop}
    {yulValid : SourceFile → YulStmt → Prop}
    {file : SourceFile} {statement : Statement}
    (valid : Statement.ValidFor expressionValid patternValid yulValid
      file statement) : statement.span.ValidFor file := by
  cases valid <;> assumption

end Statement.ValidFor

end Solcore.Syntax
