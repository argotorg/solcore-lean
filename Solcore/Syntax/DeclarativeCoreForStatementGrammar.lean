import Solcore.Syntax.DeclarativeCoreAssignmentStatementGrammar
import Solcore.Syntax.DeclarativeCoreBlockGrammar

/-!
Parser-independent grammar for Core `for` header items, item lists, and the
complete statement.

The grammar records the language priorities at each decision: `let` before an
expression item, the stop symbol before the first item, and comma before a tail
stop.  In particular, there is no derivation for a comma immediately followed
by the stop symbol.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Final source span of a Core `for`-header `let` item. -/
def forLetEnd (name : Syntax.Identifier) (type : Option Syntax.TypeExpr)
    (initializer : Option Syntax.Expr) : SourceSpan :=
  initializer.map (fun value => value.span) |>.getD
    (type.map (fun value => value.span) |>.getD name.span)

/-- Exact grammar of one `let` item in a Core `for` header. -/
inductive ForLetItemParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.ForItem → Remainder → Prop where
  | parsed {input afterMarker afterName afterType output : Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      {initializer : Option Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (initializerParsed : OptionalLetInitializerParses expressionParses
        afterType initializer output) :
      ForLetItemParses expressionParses input {
        span := SourceSpan.cover markerSpan (forLetEnd name type initializer)
        value := .letDecl name type initializer
      } output

/-- Pure construction of a non-`let` Core `for` item. -/
inductive ForAssignmentOrExpressionBuilds :
    Syntax.Expr → Option CoreAssignmentTail → Syntax.ForItem → Prop where
  | expression (left : Syntax.Expr) :
      ForAssignmentOrExpressionBuilds left none {
        span := left.span
        value := .expression left
      }
  | value (left right : Syntax.Expr) (operator : Located ValueAssignOp) :
      ForAssignmentOrExpressionBuilds left (some (.value operator right)) {
        span := SourceSpan.cover left.span right.span
        value := .assignValue left operator right
      }
  | bitNot (left : Syntax.Expr) (operator : SourceSpan) :
      ForAssignmentOrExpressionBuilds left (some (.bitNot operator)) {
        span := SourceSpan.cover left.span operator
        value := .assignBitNot left operator
      }

/-- Exact maximal assignment-or-expression item grammar. -/
def ForAssignmentOrExpressionParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (input : Remainder) (item : Syntax.ForItem) (output : Remainder) : Prop :=
  ∃ left afterLeft tail,
    expressionParses input left afterLeft ∧
      OptionalAssignmentTailParses expressionParses afterLeft tail output ∧
      ForAssignmentOrExpressionBuilds left tail item

/-- Prioritized public Core `for` item grammar. -/
inductive ForItemParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.ForItem → Remainder → Prop where
  | letItem {input output : Remainder} {item : Syntax.ForItem}
      (parsed : ForLetItemParses expressionParses input item output) :
      ForItemParses expressionParses input item output
  | assignmentOrExpression {input output : Remainder}
      {item : Syntax.ForItem}
      (letAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .letKw))
      (parsed : ForAssignmentOrExpressionParses expressionParses input item
        output) :
      ForItemParses expressionParses input item output

/-!
`ForItemsTailParses` describes the remaining forward suffix independently of
any accumulator representation.
-/
inductive ForItemsTailParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (stop : Symbol) : Remainder → List Syntax.ForItem → Remainder → Prop where
  | done {input : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .comma)) :
      ForItemsTailParses expressionParses stop input [] input
  | next {input afterComma afterItem output : Remainder}
      {item : Syntax.ForItem} {items : List Syntax.ForItem}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (stopAbsent : TokenKindAbsentAt afterComma.tokens afterComma.endIndex
        afterComma.cursor (.symbol stop))
      (itemParsed : ForItemParses expressionParses afterComma item afterItem)
      (progress : afterComma.cursor < afterItem.cursor)
      (tail : ForItemsTailParses expressionParses stop afterItem items output) :
      ForItemsTailParses expressionParses stop input (item :: items) output

/-- Exact public comma-separated item-list grammar with a prioritized stop. -/
inductive ForItemsParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (stop : Symbol) : Remainder → List Syntax.ForItem → Remainder → Prop where
  | empty {input : Remainder} (stopSpan : SourceSpan)
      (stopCurrent : TokenAt input.tokens input.endIndex input.cursor {
        span := stopSpan
        value := .symbol stop
      }) :
      ForItemsParses expressionParses stop input [] input
  | nonempty {input afterFirst output : Remainder}
      {first : Syntax.ForItem} {items : List Syntax.ForItem}
      (stopAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol stop))
      (firstParsed : ForItemParses expressionParses input first afterFirst)
      (progress : input.cursor < afterFirst.cursor)
      (tail : ForItemsTailParses expressionParses stop afterFirst items output) :
      ForItemsParses expressionParses stop input (first :: items) output

/-- Exact header, body, spans, and AST of a canonical Core `for` statement. -/
inductive ForStatementParses
    (statementParses : Remainder → Syntax.Statement → Remainder → Prop)
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition afterSecondSemicolon afterPost afterClosing output :
        Remainder}
      {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
      {body : Syntax.Block}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan
        closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsParses expressionParses .semicolon
        afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionParses afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postParsed : ForItemsParses expressionParses .rightParen
        afterSecondSemicolon post afterPost)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterPost
        closingSpan afterClosing)
      (bodyParsed : CoreBlockParses statementParses .require afterClosing body
        output) :
      ForStatementParses statementParses expressionParses input {
        span := SourceSpan.cover markerSpan body.span
        value := .forLoop (SourceSpan.cover openingSpan closingSpan)
          initializer condition post body
      } output

end Solcore.Syntax.DeclarativeGrammar
