import Solcore.Syntax.DeclarativeCoreMatchCasesOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchDefaultOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchStatementOutcomeGrammar

/-! Output functionality for diagnostic-inclusive Core match statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem requireScrutinees_outputs_eq
    {leftValues rightValues : DelimitedList Syntax.Expr}
    {input leftOutput rightOutput : Remainder}
    {left right : NonemptyDelimitedList Syntax.Expr}
    (leftParsed : RequireScrutineesOrdinaryParses leftValues input left
      leftOutput)
    (rightParsed : RequireScrutineesOrdinaryParses rightValues input right
      rightOutput) : leftOutput = rightOutput := by
  cases leftParsed
  cases rightParsed
  rfl

/-- Ordinary complete-match success has one final remainder. -/
theorem MatchStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input left afterLeft)
    (rightParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input right afterRight) :
    afterLeft = afterRight := by
  have valuesOutcomes := matchScrutineeListDeterministicOutcomeSpec
    expressionOutcomes
  have casesOutcomes := matchCasesDeterministicOutcomeSpec statementOutcomes
    patternOutcomes
  have defaultOutcomes := optionalDefaultBodyDeterministicOutcomeSpec
    statementOutcomes
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftValues leftRequired leftOpening leftCases leftDefault leftClosing =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightValues rightRequired rightOpening rightCases rightDefault
            rightClosing =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique leftValues
            rightValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq leftRequired
            rightRequired
          cases afterRequiredEq
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          cases afterOpeningEq
          have afterCasesEq := casesOutcomes.successOutputUnique leftCases
            rightCases
          cases afterCasesEq
          have afterDefaultEq := defaultOutcomes.successOutputUnique leftDefault
            rightDefault
          cases afterDefaultEq
          exact exactToken_output_unique leftClosing rightClosing

end Solcore.Syntax.DeclarativeGrammar
