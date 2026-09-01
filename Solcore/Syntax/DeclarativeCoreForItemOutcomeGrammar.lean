import Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreForStatementGrammar
import Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeGrammar

/-!
Diagnostic-inclusive ordinary success and exact rejection for one Core
`for`-header item.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev ForLetItemOrdinaryParses := ForLetItemParses

/-- Exact first rejection stage of a Core `for`-header `let` item. -/
inductive ForLetItemRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerRejected {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .letKw)) :
      ForLetItemRejects expressionOrdinary expressionRejects typeRejects
        input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      ForLetItemRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | typeRejected {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeRejected : OptionalLetTypeRejects typeRejects afterName rejected) :
      ForLetItemRejects expressionOrdinary expressionRejects typeRejects
        input rejected
  | initializerRejected
      {input afterMarker afterName afterType rejected : Remainder}
      {name : Syntax.Identifier} {type : Option Syntax.TypeExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (typeParsed : OptionalLetTypeParses afterName type afterType)
      (initializerRejected : OptionalLetInitializerRejects expressionRejects
        afterType rejected) :
      ForLetItemRejects expressionOrdinary expressionRejects typeRejects
        input rejected

abbrev ForAssignmentOrExpressionOrdinaryParses :=
  ForAssignmentOrExpressionParses

/-- The fallback item has the same two rejection stages as the terminal
assignment/expression parser before its optional semicolon stage. -/
abbrev ForAssignmentOrExpressionRejects :=
  AssignmentOrExpressionStatementRejects

abbrev ForItemOrdinaryParses := ForItemParses

/-- Exact rejection of the let-prioritized public Core `for` item. -/
inductive ForItemRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | letItem {input rejected : Remainder} {markerSpan : SourceSpan}
      (markerCurrent : TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .keyword .letKw
      })
      (itemRejected : ForLetItemRejects expressionOrdinary expressionRejects
        typeRejects input rejected) :
      ForItemRejects expressionOrdinary expressionRejects typeRejects input
        rejected
  | assignmentOrExpression {input rejected : Remainder}
      (letAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .letKw))
      (itemRejected : ForAssignmentOrExpressionRejects expressionOrdinary
        expressionRejects input rejected) :
      ForItemRejects expressionOrdinary expressionRejects typeRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
