import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreForItemsOutcomeProperties
import Solcore.Syntax.DeclarativeCoreForStatementOutcomeGrammar

/-! Functional ordinary success for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- Ordinary Core `for` success has one final remainder. -/
theorem ForStatementOrdinaryParses.output_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input left afterLeft)
    (rightParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input right afterRight) : afterLeft = afterRight := by
  have initializerOutcomes := forItemsDeterministicOutcomeSpec
    expressionOutcomes .semicolon
  have postOutcomes := forItemsDeterministicOutcomeSpec expressionOutcomes
    .rightParen
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftFirstSemicolonSpan
        leftSecondSemicolonSpan leftClosingSpan leftMarker leftOpening
        leftInitializer leftFirstSemicolon leftCondition leftSecondSemicolon
        leftPost leftClosing leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightFirstSemicolonSpan
            rightSecondSemicolonSpan rightClosingSpan rightMarker rightOpening
            rightInitializer rightFirstSemicolon rightCondition
            rightSecondSemicolon rightPost rightClosing rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            leftInitializer rightInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            leftFirstSemicolon rightFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            leftCondition rightCondition
          subst afterConditionEq
          have afterSecondSemicolonEq := exactToken_output_unique
            leftSecondSemicolon rightSecondSemicolon
          subst afterSecondSemicolonEq
          have afterPostEq := postOutcomes.successOutputUnique leftPost
            rightPost
          subst afterPostEq
          have afterClosingEq := exactToken_output_unique leftClosing
            rightClosing
          subst afterClosingEq
          exact blockOutcomes.successOutputUnique leftBody rightBody

end Solcore.Syntax.DeclarativeGrammar
