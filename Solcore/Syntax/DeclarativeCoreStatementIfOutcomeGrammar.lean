import Solcore.Syntax.DeclarativeCoreBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementControlGrammar

/-! Ordinary successes and exact rejections for canonical Core `if`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive optional-else success over raw Core blocks. -/
abbrev OptionalElseBodyOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop) :=
  OptionalElseBodyParses
    (CoreBlockOrdinaryParses statementOrdinary .require)

/-- A present optional `else` rejects exactly through its required body. -/
inductive OptionalElseBodyRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | bodyRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .elseKw) input markerSpan
        afterMarker)
      (bodyRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterMarker rejected) :
      OptionalElseBodyRejects statementOrdinary statementRejects input rejected

/-- Diagnostic-inclusive complete Core `if` success. -/
abbrev IfStatementOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop) :=
  IfStatementParses expressionOrdinary
    (CoreBlockOrdinaryParses statementOrdinary .require)

/-- Exact first rejection stage of one canonical Core `if` statement. -/
inductive IfStatementRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .ifKw)) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input input
  | openingMissing {input afterMarker : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .leftParen)) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input afterMarker
  | conditionRejected {input afterMarker afterOpening rejected : Remainder}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionRejected : expressionRejects afterOpening rejected) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected
  | closingMissing
      {input afterMarker afterOpening afterCondition : Remainder}
      {condition : Syntax.Expr} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingAbsent : TokenKindAbsentAt afterCondition.tokens
        afterCondition.endIndex afterCondition.cursor (.symbol .rightParen)) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input afterCondition
  | thenRejected
      {input afterMarker afterOpening afterCondition afterClosing rejected :
        Remainder}
      {condition : Syntax.Expr}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (thenRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterClosing rejected) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected
  | elseRejected
      {input afterMarker afterOpening afterCondition afterClosing afterThen
        rejected : Remainder}
      {condition : Syntax.Expr} {thenBody : Syntax.Block}
      (markerSpan openingSpan closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (conditionParsed : expressionOrdinary afterOpening condition
        afterCondition)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterCondition
        closingSpan afterClosing)
      (thenParsed : CoreBlockOrdinaryParses statementOrdinary .require
        afterClosing thenBody afterThen)
      (elseRejected : OptionalElseBodyRejects statementOrdinary
        statementRejects afterThen rejected) :
      IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
