import Solcore.Syntax.DeclarativeCoreBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreForItemsOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreForStatementGrammar

/-! Diagnostic-inclusive ordinary success and exact rejection for Core `for`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Complete ordinary Core `for` success, including diagnosed recursive body
outcomes. -/
inductive ForStatementOrdinaryParses
    (statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | parsed {input afterMarker afterOpening afterInitializer
      afterFirstSemicolon afterCondition afterSecondSemicolon afterPost
      afterClosing output : Remainder}
      {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
      {body : Syntax.Block}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan
        closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postParsed : ForItemsOrdinaryParses expressionOrdinary .rightParen
        afterSecondSemicolon post afterPost)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterPost
        closingSpan afterClosing)
      (bodyParsed : CoreBlockOrdinaryParses statementOrdinary .require
        afterClosing body output) :
      ForStatementOrdinaryParses statementOrdinary expressionOrdinary input {
        span := SourceSpan.cover markerSpan body.span
        value := .forLoop (SourceSpan.cover openingSpan closingSpan)
          initializer condition post body
      } output

/-- Exact first rejected stage of a complete Core `for` statement. -/
inductive ForStatementRejects
    (statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .forKw)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input input
  | openingMissing {input afterMarker : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .leftParen)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input afterMarker
  | initializerRejected {input afterMarker afterOpening rejected : Remainder}
      (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerRejected : ForItemsRejects expressionOrdinary
        expressionRejects .semicolon afterOpening rejected) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input rejected
  | firstSemicolonMissing
      {input afterMarker afterOpening afterInitializer : Remainder}
      {initializer : List Syntax.ForItem} (markerSpan openingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (semicolonAbsent : TokenKindAbsentAt afterInitializer.tokens
        afterInitializer.endIndex afterInitializer.cursor
          (.symbol .semicolon)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input afterInitializer
  | conditionRejected
      {input afterMarker afterOpening afterInitializer afterSemicolon
        rejected : Remainder}
      {initializer : List Syntax.ForItem}
      (markerSpan openingSpan semicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer semicolonSpan afterSemicolon)
      (conditionRejected : expressionRejects afterSemicolon rejected) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input rejected
  | secondSemicolonMissing
      {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition : Remainder}
      {initializer : List Syntax.ForItem} {condition : Syntax.Expr}
      (markerSpan openingSpan firstSemicolonSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (semicolonAbsent : TokenKindAbsentAt afterCondition.tokens
        afterCondition.endIndex afterCondition.cursor (.symbol .semicolon)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input afterCondition
  | postRejected
      {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition afterSecondSemicolon rejected : Remainder}
      {initializer : List Syntax.ForItem} {condition : Syntax.Expr}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan :
        SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postRejected : ForItemsRejects expressionOrdinary expressionRejects
        .rightParen afterSecondSemicolon rejected) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input rejected
  | closingMissing
      {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition afterSecondSemicolon afterPost : Remainder}
      {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan :
        SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postParsed : ForItemsOrdinaryParses expressionOrdinary .rightParen
        afterSecondSemicolon post afterPost)
      (closingAbsent : TokenKindAbsentAt afterPost.tokens afterPost.endIndex
        afterPost.cursor (.symbol .rightParen)) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input afterPost
  | bodyRejected
      {input afterMarker afterOpening afterInitializer afterFirstSemicolon
        afterCondition afterSecondSemicolon afterPost afterClosing rejected :
        Remainder}
      {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
      (markerSpan openingSpan firstSemicolonSpan secondSemicolonSpan
        closingSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
        openingSpan afterOpening)
      (initializerParsed : ForItemsOrdinaryParses expressionOrdinary
        .semicolon afterOpening initializer afterInitializer)
      (firstSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterInitializer firstSemicolonSpan afterFirstSemicolon)
      (conditionParsed : expressionOrdinary afterFirstSemicolon condition
        afterCondition)
      (secondSemicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterCondition secondSemicolonSpan afterSecondSemicolon)
      (postParsed : ForItemsOrdinaryParses expressionOrdinary .rightParen
        afterSecondSemicolon post afterPost)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterPost
        closingSpan afterClosing)
      (bodyRejected : CoreBlockRejects statementOrdinary statementRejects
        .require afterClosing rejected) :
      ForStatementRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
