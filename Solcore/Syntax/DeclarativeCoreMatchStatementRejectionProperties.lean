import Solcore.Syntax.DeclarativeCoreMatchStatementOrdinaryProperties

/-! Rejection exclusivity for diagnostic-inclusive Core match statements. -/

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

private theorem scrutineeList_conflicts_requireReject
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input afterValues rejected : Remainder}
    {values : DelimitedList Syntax.Expr}
    (valuesParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      values afterValues)
    (requiredRejected : RequireScrutineesRejects values afterValues rejected) :
    False := by
  rcases valuesParsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  cases requiredRejected with
  | empty emptyValues =>
      have impossible : first :: rest = [] := elementsEq.symm.trans emptyValues
      contradiction

/-- Exact pre-validation rejection excludes every ordinary match success. -/
theorem MatchStatementRejects.disjointOrdinary
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
    {input rejected : Remainder}
    (rejection : MatchStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects
        input rejected) :
    ¬ ∃ value output,
      MatchStatementOrdinaryParses statementOrdinary expressionOrdinary
        patternOrdinary input value output := by
  rintro ⟨value, output, successful⟩
  have valuesOutcomes := matchScrutineeListDeterministicOutcomeSpec
    expressionOutcomes
  have casesOutcomes := matchCasesDeterministicOutcomeSpec statementOutcomes
    patternOutcomes
  have defaultOutcomes := optionalDefaultBodyDeterministicOutcomeSpec
    statementOutcomes
  cases successful with
  | parsed successfulMarkerSpan successfulOpeningSpan successfulClosingSpan
        successfulMarker successfulValues successfulRequired
        successfulOpening successfulCases successfulDefault
        successfulClosing =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | valuesRejected rejectedMarkerSpan rejectedMarker rejectedValues =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact valuesOutcomes.successRejectDisjoint rejectedValues
            ⟨_, _, successfulValues⟩
      | scrutineesRejected rejectedMarkerSpan rejectedMarker rejectedValues
            rejectedRequired =>
          exact scrutineeList_conflicts_requireReject rejectedValues
            rejectedRequired
      | openingMissing rejectedMarkerSpan rejectedMarker rejectedValues
            rejectedRequired openingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique
            rejectedValues successfulValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq
            rejectedRequired successfulRequired
          cases afterRequiredEq
          exact absent_conflicts_exact openingAbsent successfulOpening
      | casesRejected rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedValues rejectedRequired rejectedOpening rejectedCases =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique
            rejectedValues successfulValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq
            rejectedRequired successfulRequired
          cases afterRequiredEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          exact casesOutcomes.successRejectDisjoint rejectedCases
            ⟨_, _, successfulCases⟩
      | defaultRejected rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedValues rejectedRequired rejectedOpening rejectedCases
            rejectedDefault =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique
            rejectedValues successfulValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq
            rejectedRequired successfulRequired
          cases afterRequiredEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          have afterCasesEq := casesOutcomes.successOutputUnique rejectedCases
            successfulCases
          cases afterCasesEq
          exact defaultOutcomes.successRejectDisjoint rejectedDefault
            ⟨_, _, successfulDefault⟩
      | closingMissing rejectedMarkerSpan rejectedOpeningSpan rejectedMarker
            rejectedValues rejectedRequired rejectedOpening rejectedCases
            rejectedDefault closingAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterValuesEq := valuesOutcomes.successOutputUnique
            rejectedValues successfulValues
          cases afterValuesEq
          have afterRequiredEq := requireScrutinees_outputs_eq
            rejectedRequired successfulRequired
          cases afterRequiredEq
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            successfulOpening
          cases afterOpeningEq
          have afterCasesEq := casesOutcomes.successOutputUnique rejectedCases
            successfulCases
          cases afterCasesEq
          have afterDefaultEq := defaultOutcomes.successOutputUnique
            rejectedDefault successfulDefault
          cases afterDefaultEq
          exact absent_conflicts_exact closingAbsent successfulClosing

end Solcore.Syntax.DeclarativeGrammar
