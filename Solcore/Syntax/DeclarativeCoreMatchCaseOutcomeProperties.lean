import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchComponentOutcomeGrammar

/-! Deterministic diagnostic-inclusive outcomes for one Core match case. -/

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

/-- Ordinary match-case success has one final remainder. -/
theorem MatchCaseOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : afterLeft = afterRight := by
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftPattern leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightPattern rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          cases afterMarkerEq
          have afterPatternEq := patternOutcomes.successOutputUnique
            leftPattern rightPattern
          cases afterPatternEq
          exact blockOutcomes.successOutputUnique leftBody rightBody

/-- Exact match-case rejection excludes ordinary success. -/
theorem MatchCaseRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input rejected : Remainder}
    (rejection : MatchCaseRejects statementOrdinary statementRejects
      patternOrdinary patternRejects input rejected) :
    ¬ ∃ arm output,
      MatchCaseOrdinaryParses statementOrdinary patternOrdinary input arm
        output := by
  rintro ⟨arm, output, successful⟩
  have blockOutcomes := coreBlockDeterministicOutcomeSpec .require
    statementOutcomes
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulPattern
        successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | patternRejected rejectedMarkerSpan rejectedMarker rejectedPattern =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          exact patternOutcomes.successRejectDisjoint rejectedPattern
            ⟨_, _, successfulPattern⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedPattern
            rejectedBody =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          cases afterMarkerEq
          have afterPatternEq := patternOutcomes.successOutputUnique
            rejectedPattern successfulPattern
          cases afterPatternEq
          exact blockOutcomes.successRejectDisjoint rejectedBody
            ⟨_, _, successfulBody⟩

/-- Lift statement and pattern outcomes through one Core match case. -/
theorem matchCaseDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : DeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    DeterministicOutcomeSpec
      (MatchCaseOrdinaryParses statementOrdinary patternOrdinary)
      (MatchCaseRejects statementOrdinary statementRejects patternOrdinary
        patternRejects) where
  successOutputUnique := MatchCaseOrdinaryParses.output_unique
    statementOutcomes patternOutcomes
  successRejectDisjoint := MatchCaseRejects.disjointOrdinary
    statementOutcomes patternOutcomes

/-- Every clean match-case derivation embeds into the ordinary relation. -/
theorem MatchCaseParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {patternClean patternOrdinary :
      Remainder → Syntax.Pattern → Remainder → Prop}
    (statementToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    (patternToOrdinary : ∀ {input pattern output},
      patternClean input pattern output →
        patternOrdinary input pattern output)
    {input output : Remainder} {arm : Syntax.MatchCase}
    (parsed : MatchCaseParses statementClean patternClean input arm output) :
    MatchCaseOrdinaryParses statementOrdinary patternOrdinary input arm
      output := by
  cases parsed with
  | parsed markerSpan markerParsed patternParsed bodyParsed =>
      exact .parsed markerSpan markerParsed
        (patternToOrdinary patternParsed)
        (bodyParsed.toOrdinary statementToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
