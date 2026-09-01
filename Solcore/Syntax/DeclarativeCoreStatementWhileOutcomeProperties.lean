import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementWhileOutcomeGrammar

/-! Deterministic ordinary outcomes for canonical Core `while`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Ordinary Core `while` success has one final remainder. -/
theorem WhileStatementOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) : afterLeft = afterRight := by
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftOpening leftCondition leftClosing leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightOpening rightCondition rightClosing rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          cases afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            leftCondition rightCondition
          cases afterConditionEq
          have afterClosingEq := exactToken_output_unique leftClosing
            rightClosing
          cases afterClosingEq
          exact blockOutcomes.successOutputUnique leftBody rightBody

/-- Exact Core `while` rejection excludes ordinary success. -/
theorem WhileStatementRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : WhileStatementRejects expressionOrdinary expressionRejects
      statementOrdinary statementRejects input rejected) :
    ¬ ∃ statement output,
      WhileStatementOrdinaryParses expressionOrdinary statementOrdinary input
        statement output := by
  rintro ⟨statement, output, successful⟩
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases successful with
  | parsed successfulMarkerSpan successfulOpeningSpan successfulClosingSpan
        successfulMarker successfulOpening successfulCondition
        successfulClosing successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | openingMissing rejectedMarkerSpan rejectedMarker openingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact absent_conflicts_exact openingAbsent successfulOpening
      | conditionRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedMarker rejectedOpening rejectedCondition =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          exact expressionOutcomes.successRejectDisjoint rejectedCondition
            ⟨_, _, successfulCondition⟩
      | closingMissing rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedOpening rejectedCondition closingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          cases afterConditionEq
          exact absent_conflicts_exact closingAbsent successfulClosing
      | bodyRejected rejectedMarkerSpan rejectedOpeningSpan rejectedClosingSpan
            rejectedMarker rejectedOpening rejectedCondition rejectedClosing
            rejectedBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          cases afterConditionEq
          have afterClosingEq := exactToken_output_unique rejectedClosing
            successfulClosing
          cases afterClosingEq
          exact blockOutcomes.successRejectDisjoint rejectedBody
            ⟨_, _, successfulBody⟩

/-- Lift expression and recursive-statement outcomes through one Core
`while` statement. -/
theorem whileStatementDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (WhileStatementOrdinaryParses expressionOrdinary statementOrdinary)
      (WhileStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects) where
  successOutputUnique := WhileStatementOrdinaryParses.output_unique
    expressionOutcomes statementOutcomes
  successRejectDisjoint := WhileStatementRejects.disjointOrdinary
    expressionOutcomes statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
