import Solcore.Syntax.DeclarativeCorePatternComptimeOutcomeGrammar

/-! Deterministic ordinary outcomes for Core compile-time patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (left : ExactTokenParses kind input leftSpan leftOutput)
    (right : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [left.2, right.2]

private theorem tokenAbsent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Ordinary compile-time-pattern success has one output remainder. -/
theorem ComptimePatternOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Pattern}
    {afterLeft afterRight : Remainder}
    (leftParsed : ComptimePatternOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ComptimePatternOrdinaryParses expressionOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftExpression =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightExpression =>
          have markerOutputEq := exactToken_output_unique leftMarker rightMarker
          cases markerOutputEq
          exact expressionOutcomes.successOutputUnique leftExpression
            rightExpression

/-- Exact compile-time-pattern rejection excludes ordinary success. -/
theorem ComptimePatternRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ComptimePatternRejects expressionRejects input rejected) :
    ¬ ∃ pattern output,
      ComptimePatternOrdinaryParses expressionOrdinary input pattern output := by
  rintro ⟨pattern, output, parsed⟩
  cases rejection with
  | markerMissing markerAbsent =>
      cases parsed with
      | parsed markerSpan markerParsed expressionParsed =>
          exact tokenAbsent_conflicts_exact markerAbsent markerParsed
  | expressionRejected rejectedMarkerSpan rejectedMarker rejectedExpression =>
      cases parsed with
      | parsed parsedMarkerSpan parsedMarker parsedExpression =>
          have markerOutputEq := exactToken_output_unique rejectedMarker
            parsedMarker
          cases markerOutputEq
          exact expressionOutcomes.successRejectDisjoint rejectedExpression
            ⟨_, _, parsedExpression⟩

/-- Lift deterministic expression outcomes through a compile-time pattern. -/
theorem comptimePatternDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ComptimePatternOrdinaryParses expressionOrdinary)
      (ComptimePatternRejects expressionRejects) where
  successOutputUnique :=
    ComptimePatternOrdinaryParses.output_unique
      expressionOutcomes
  successRejectDisjoint :=
    ComptimePatternRejects.disjointOrdinary expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
