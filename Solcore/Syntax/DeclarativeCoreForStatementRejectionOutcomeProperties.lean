import Solcore.Syntax.DeclarativeCoreForStatementSuccessOutcomeProperties

/-! Rejection disjointness for complete Core `for` statements. -/

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

/-- Exact Core `for` rejection excludes ordinary success. -/
theorem ForStatementRejects.disjointOrdinary
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ForStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects input rejected) :
    ¬ ∃ statement output, ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input statement output := by
  rintro ⟨statement, output, successful⟩
  have initializerOutcomes := forItemsDeterministicOutcomeSpec
    expressionOutcomes .semicolon
  have postOutcomes := forItemsDeterministicOutcomeSpec expressionOutcomes
    .rightParen
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases successful with
  | parsed successfulMarkerSpan successfulOpeningSpan
        successfulFirstSemicolonSpan successfulSecondSemicolonSpan
        successfulClosingSpan successfulMarker successfulOpening
        successfulInitializer successfulFirstSemicolon successfulCondition
        successfulSecondSemicolon successfulPost successfulClosing
        successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | openingMissing rejectedMarkerSpan rejectedMarker openingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact absent_conflicts_exact openingAbsent successfulOpening
      | initializerRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedMarker rejectedOpening rejectedInitializer =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          exact initializerOutcomes.successRejectDisjoint
            rejectedInitializer ⟨_, _, successfulInitializer⟩
      | firstSemicolonMissing rejectedMarkerSpan rejectedOpeningSpan
            rejectedMarker rejectedOpening rejectedInitializer
            semicolonAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          exact absent_conflicts_exact semicolonAbsent
            successfulFirstSemicolon
      | conditionRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedSemicolonSpan rejectedMarker rejectedOpening
            rejectedInitializer rejectedSemicolon rejectedCondition =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterSemicolonEq := exactToken_output_unique rejectedSemicolon
            successfulFirstSemicolon
          subst afterSemicolonEq
          exact expressionOutcomes.successRejectDisjoint rejectedCondition
            ⟨_, _, successfulCondition⟩
      | secondSemicolonMissing rejectedMarkerSpan rejectedOpeningSpan
            rejectedFirstSemicolonSpan rejectedMarker rejectedOpening
            rejectedInitializer rejectedFirstSemicolon rejectedCondition
            semicolonAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            rejectedFirstSemicolon successfulFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          exact absent_conflicts_exact semicolonAbsent
            successfulSecondSemicolon
      | postRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedFirstSemicolonSpan rejectedSecondSemicolonSpan
            rejectedMarker rejectedOpening rejectedInitializer
            rejectedFirstSemicolon rejectedCondition rejectedSecondSemicolon
            rejectedPost =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            rejectedFirstSemicolon successfulFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterSecondSemicolonEq := exactToken_output_unique
            rejectedSecondSemicolon successfulSecondSemicolon
          subst afterSecondSemicolonEq
          exact postOutcomes.successRejectDisjoint rejectedPost
            ⟨_, _, successfulPost⟩
      | closingMissing rejectedMarkerSpan rejectedOpeningSpan
            rejectedFirstSemicolonSpan rejectedSecondSemicolonSpan
            rejectedMarker rejectedOpening rejectedInitializer
            rejectedFirstSemicolon rejectedCondition rejectedSecondSemicolon
            rejectedPost closingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            rejectedFirstSemicolon successfulFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterSecondSemicolonEq := exactToken_output_unique
            rejectedSecondSemicolon successfulSecondSemicolon
          subst afterSecondSemicolonEq
          have afterPostEq := postOutcomes.successOutputUnique rejectedPost
            successfulPost
          subst afterPostEq
          exact absent_conflicts_exact closingAbsent successfulClosing
      | bodyRejected rejectedMarkerSpan rejectedOpeningSpan
            rejectedFirstSemicolonSpan rejectedSecondSemicolonSpan
            rejectedClosingSpan rejectedMarker rejectedOpening
            rejectedInitializer rejectedFirstSemicolon rejectedCondition
            rejectedSecondSemicolon rejectedPost rejectedClosing
            rejectedBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          subst afterOpeningEq
          have afterInitializerEq := initializerOutcomes.successOutputUnique
            rejectedInitializer successfulInitializer
          subst afterInitializerEq
          have afterFirstSemicolonEq := exactToken_output_unique
            rejectedFirstSemicolon successfulFirstSemicolon
          subst afterFirstSemicolonEq
          have afterConditionEq := expressionOutcomes.successOutputUnique
            rejectedCondition successfulCondition
          subst afterConditionEq
          have afterSecondSemicolonEq := exactToken_output_unique
            rejectedSecondSemicolon successfulSecondSemicolon
          subst afterSecondSemicolonEq
          have afterPostEq := postOutcomes.successOutputUnique rejectedPost
            successfulPost
          subst afterPostEq
          have afterClosingEq := exactToken_output_unique rejectedClosing
            successfulClosing
          subst afterClosingEq
          exact blockOutcomes.successRejectDisjoint rejectedBody
            ⟨_, _, successfulBody⟩

end Solcore.Syntax.DeclarativeGrammar
