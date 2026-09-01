import Solcore.Syntax.DeclarativeCoreBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementControlGrammar

/-! Ordinary success and exact rejection for canonical Core `while`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive `while` success with an ordinary condition and raw
required-policy Core block. -/
abbrev WhileStatementOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop) :=
  WhileStatementParses expressionOrdinary
    (CoreBlockOrdinaryParses statementOrdinary .require)

/-- Exact first-failing stage of a canonical Core `while` statement.  The
marker remains an identifier token because `while` is contextual. -/
inductive WhileStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.while.spelling)) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input input
  | openingMissing {input afterMarker : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .leftParen)) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input afterMarker
  | conditionRejected
      {input afterMarker afterOpening rejected : Remainder}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (rejectedCondition : expressionRejects afterOpening rejected) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected
  | closingMissing
      {input afterMarker afterOpening afterCondition : Remainder}
      {condition : Syntax.Expr} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingAbsent : TokenKindAbsentAt afterCondition.tokens
        afterCondition.endIndex afterCondition.cursor (.symbol .rightParen)) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input afterCondition
  | bodyRejected
      {input afterMarker afterOpening afterCondition afterClosing rejected :
        Remainder}
      {condition : Syntax.Expr}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.while.spelling) input markerSpan
          afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (rejectedBody : CoreBlockRejects statementOrdinary statementRejects
        .require afterClosing rejected) :
      WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
