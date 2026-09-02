import Solcore.Syntax.DeclarativePredicateSequenceOutcomeProperties
import Solcore.Syntax.DeclarativeWhereClauseOutcomeGrammar

/-! Deterministic exact outcomes for optional canonical `where` clauses. -/

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

/-- Optional `where` success has one final remainder. -/
theorem OptionalWhereClauseParses.output_unique
    {input : Remainder} {left right : Option Syntax.WhereClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalWhereClauseParses input left afterLeft)
    (rightParsed : OptionalWhereClauseParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightMarkerSpan rightMarker rightPredicates =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftPredicates =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightPredicates =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact PredicateSequenceParses.output_unique leftPredicates
            rightPredicates

/-- Exact optional-`where` rejection excludes every successful branch. -/
theorem OptionalWhereClauseRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalWhereClauseRejects input rejected) :
    ¬ ∃ clause output, OptionalWhereClauseParses input clause output := by
  rintro ⟨clause, output, successful⟩
  cases rejection with
  | predicatesRejected rejectedMarkerSpan rejectedMarker
        predicatesRejected =>
      cases successful with
      | absent markerAbsent =>
          exact absent_conflicts_exact markerAbsent rejectedMarker
      | present successfulMarkerSpan successfulMarker predicatesParsed =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact predicateSequenceDeterministicOutcomeSpec.successRejectDisjoint
            predicatesRejected ⟨_, _, predicatesParsed⟩

/-- Optional canonical `where` has deterministic and exclusive outcomes. -/
theorem optionalWhereClauseDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalWhereClauseParses
      OptionalWhereClauseRejects where
  successOutputUnique := OptionalWhereClauseParses.output_unique
  successRejectDisjoint := OptionalWhereClauseRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
