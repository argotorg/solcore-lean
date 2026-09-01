import Solcore.Syntax.DeclarativeCoreStatementOptionalElseOutcomeProperties

/-! Deterministic diagnostic-inclusive outcomes for canonical Core `if`. -/

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

/-- Ordinary Core `if` success has one final remainder. -/
theorem IfStatementOrdinaryParses.output_unique
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
    (leftParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftOpening leftCondition leftClosing leftThen leftElse =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightOpening rightCondition rightClosing rightThen rightElse =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique leftOpening
            rightOpening
          subst afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            leftCondition rightCondition
          subst afterConditionEq
          have afterClosingEq := exactToken_output_unique leftClosing
            rightClosing
          subst afterClosingEq
          have afterThenEq := leftThen.output_unique statementOutcomes
            rightThen
          subst afterThenEq
          exact OptionalElseBodyOrdinaryParses.output_unique statementOutcomes
            leftElse rightElse

/-- Exact Core `if` rejection excludes ordinary success. -/
theorem IfStatementRejects.disjointOrdinary
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
    (rejection : IfStatementRejects expressionOrdinary expressionRejects
      statementOrdinary statementRejects input rejected) :
    ¬ ∃ statement output,
      IfStatementOrdinaryParses expressionOrdinary statementOrdinary input
        statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulOpeningSpan successfulClosingSpan
        successfulMarker successfulOpening successfulCondition
        successfulClosing successfulThen successfulElse =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | openingMissing rejectedMarkerSpan rejectedMarker openingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact absent_conflicts_exact openingAbsent successfulOpening
      | conditionRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedMarker rejectedOpening rejectedCondition =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact expressionOutcomes.successRejectDisjoint rejectedCondition
            ⟨_, _, successfulCondition⟩
      | closingMissing rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedOpening rejectedCondition closingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          exact absent_conflicts_exact closingAbsent successfulClosing
      | thenRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedClosingSpan rejectedMarker rejectedOpening
            rejectedCondition rejectedClosing rejectedThen =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterClosingEq := exactToken_output_unique rejectedClosing
            successfulClosing
          subst afterClosingEq
          exact rejectedThen.disjointOrdinary statementOutcomes
            ⟨_, _, successfulThen⟩
      | elseRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedClosingSpan rejectedMarker rejectedOpening
            rejectedCondition rejectedClosing rejectedThen rejectedElse =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterClosingEq := exactToken_output_unique rejectedClosing
            successfulClosing
          subst afterClosingEq
          have afterThenEq := rejectedThen.output_unique statementOutcomes
            successfulThen
          subst afterThenEq
          exact (OptionalElseBodyRejects.disjointOrdinary statementOutcomes
            rejectedElse) ⟨_, _, successfulElse⟩

/-- Lift expression and recursive statement outcomes through Core `if`. -/
theorem ifStatementDeterministicOutcomeSpec
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
      (IfStatementOrdinaryParses expressionOrdinary statementOrdinary)
      (IfStatementRejects expressionOrdinary expressionRejects
        statementOrdinary statementRejects) where
  successOutputUnique := IfStatementOrdinaryParses.output_unique
    expressionOutcomes statementOutcomes
  successRejectDisjoint := IfStatementRejects.disjointOrdinary
    expressionOutcomes statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
