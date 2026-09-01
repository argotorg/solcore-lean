import Solcore.Syntax.DeclarativeYulBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeYulExpressionFuelGrammar
import Solcore.Syntax.DeclarativeYulStatementControlGrammar

/-!
Parser-independent ordinary successes and exact rejection traces for inline-
Yul `if` and `for` primaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary `if` success reuses the exact control grammar with ordinary
recursive statement and public expression relations. -/
abbrev YulIfStatementOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulIfStatementParses statementOrdinary YulExpressionOrdinaryParses

/-- Exact rejection stage of an inline-Yul `if` primary. -/
inductive YulIfStatementRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .ifKw)) :
      YulIfStatementRejects statementOrdinary statementRejects input input
  | conditionRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (conditionRejected : YulExpressionRejects afterMarker rejected) :
      YulIfStatementRejects statementOrdinary statementRejects input rejected
  | bodyRejected {input afterMarker afterCondition rejected : Remainder}
      {condition : Syntax.YulExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (conditionParsed : YulExpressionOrdinaryParses afterMarker condition
        afterCondition)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterCondition rejected) :
      YulIfStatementRejects statementOrdinary statementRejects input rejected

/-- Ordinary `for` success reuses the exact control grammar with ordinary
recursive statement and public expression relations. -/
abbrev YulForStatementOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulForStatementParses statementOrdinary YulExpressionOrdinaryParses

/-- Exact rejection stage of an inline-Yul `for` primary. -/
inductive YulForStatementRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .forKw)) :
      YulForStatementRejects statementOrdinary statementRejects input input
  | initializerRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerRejected : YulBlockRejects statementOrdinary
        statementRejects afterMarker rejected) :
      YulForStatementRejects statementOrdinary statementRejects input rejected
  | conditionRejected
      {input afterMarker afterInitializer rejected : Remainder}
      {initializerSpan : SourceSpan}
      {initializer : List Syntax.YulStmt} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerParsed : YulBlockOrdinaryParses statementOrdinary afterMarker
        initializerSpan initializer afterInitializer)
      (conditionRejected : YulExpressionRejects afterInitializer rejected) :
      YulForStatementRejects statementOrdinary statementRejects input rejected
  | postRejected
      {input afterMarker afterInitializer afterCondition rejected : Remainder}
      {initializerSpan : SourceSpan}
      {initializer : List Syntax.YulStmt} {condition : Syntax.YulExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerParsed : YulBlockOrdinaryParses statementOrdinary afterMarker
        initializerSpan initializer afterInitializer)
      (conditionParsed : YulExpressionOrdinaryParses afterInitializer condition
        afterCondition)
      (postRejected : YulBlockRejects statementOrdinary statementRejects
        afterCondition rejected) :
      YulForStatementRejects statementOrdinary statementRejects input rejected
  | bodyRejected
      {input afterMarker afterInitializer afterCondition afterPost rejected :
        Remainder}
      {initializerSpan postSpan : SourceSpan}
      {initializer post : List Syntax.YulStmt} {condition : Syntax.YulExpr}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerParsed : YulBlockOrdinaryParses statementOrdinary afterMarker
        initializerSpan initializer afterInitializer)
      (conditionParsed : YulExpressionOrdinaryParses afterInitializer condition
        afterCondition)
      (postParsed : YulBlockOrdinaryParses statementOrdinary afterCondition
        postSpan post afterPost)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterPost rejected) :
      YulForStatementRejects statementOrdinary statementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
