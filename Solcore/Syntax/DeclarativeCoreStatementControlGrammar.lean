import Solcore.Syntax.DeclarativeCoreBlockGrammar

/-!
Parser-independent grammar for Core block, terminated-control, while, and if
statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A Core block retained as one statement. -/
inductive BlockStatementParses
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input output : Remainder} {body : Syntax.Block}
      (bodyParsed : blockParses input body output) :
      BlockStatementParses blockParses input {
        span := body.span
        value := .block body.value
      } output

/-- Exact keyword-plus-semicolon grammar shared by `break` and `continue`. -/
inductive TerminatedControlStatementParses
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      (markerSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword keyword) input markerSpan
        afterMarker)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) afterMarker
        semicolonSpan output) :
      TerminatedControlStatementParses keyword statementValue input {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := statementValue
      } output

/-- Prioritized optional `else` body. -/
inductive OptionalElseBodyParses
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Option Syntax.Block → Remainder → Prop where
  | absent {input : Remainder}
      (elseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .elseKw)) :
      OptionalElseBodyParses blockParses input none input
  | present {input afterMarker output : Remainder} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .elseKw) input markerSpan
        afterMarker)
      (bodyParsed : blockParses afterMarker body output) :
      OptionalElseBodyParses blockParses input (some body) output

/-- Exact canonical Core `while` statement grammar. -/
inductive WhileStatementParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterOpening afterCondition afterClosing output :
        Remainder}
      {condition : Syntax.Expr} {body : Syntax.Block}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionParses afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (bodyParsed : blockParses afterClosing body output) :
      WhileStatementParses expressionParses blockParses input {
        span := SourceSpan.cover markerSpan body.span
        value := .whileLoop condition body
      } output

/-- Exact canonical Core `if` statement grammar with prioritized optional
`else`. -/
inductive IfStatementParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterOpening afterCondition afterClosing
        afterThen output : Remainder}
      {condition : Syntax.Expr} {thenBody : Syntax.Block}
      {elseBody : Option Syntax.Block}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionParses afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (thenParsed : blockParses afterClosing thenBody afterThen)
      (elseParsed : OptionalElseBodyParses blockParses afterThen elseBody
        output) :
      IfStatementParses expressionParses blockParses input {
        span := SourceSpan.cover markerSpan
          (elseBody.map (fun body => body.span) |>.getD thenBody.span)
        value := .ifThen condition thenBody elseBody
      } output

end Solcore.Syntax.DeclarativeGrammar
