import Solcore.Syntax.DeclarativePredicateSequenceExactnessProperties
import Solcore.Syntax.DeclarativeWhereClauseOutcomeProperties

/-! Exact values and rejection endpoints for optional `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem where_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An optional `where` clause fixes its absent or present AST value. -/
theorem OptionalWhereClauseParses.value_unique
    {input : Remainder} {left right : Option Syntax.WhereClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalWhereClauseParses input left afterLeft)
    (rightParsed : OptionalWhereClauseParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightMarkerSpan rightMarker rightPredicates =>
          exact False.elim
            (where_absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftPredicates =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (where_absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightPredicates =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          have predicatesEq :=
            predicateSequenceExactOutcomeSpec.successValueUnique
              leftPredicates rightPredicates
          subst predicatesEq
          rfl

/-- An optional `where` clause fixes its AST and final remainder. -/
theorem OptionalWhereClauseParses.result_unique
    {input : Remainder} {left right : Option Syntax.WhereClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalWhereClauseParses input left afterLeft)
    (rightParsed : OptionalWhereClauseParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A committed `where` rejection has one first failing endpoint. -/
theorem OptionalWhereClauseRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalWhereClauseRejects input left)
    (rightRejected : OptionalWhereClauseRejects input right) :
    left = right := by
  cases leftRejected with
  | predicatesRejected _ leftMarker leftPredicates =>
      cases rightRejected with
      | predicatesRejected _ rightMarker rightPredicates =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          exact predicateSequenceExactOutcomeSpec.rejectOutputUnique
            leftPredicates rightPredicates

/-- Optional `where` clauses have fully exact ordinary outcomes. -/
theorem optionalWhereClauseExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalWhereClauseParses
      OptionalWhereClauseRejects where
  toDeterministicOutcomeSpec := optionalWhereClauseDeterministicOutcomeSpec
  successValueUnique := OptionalWhereClauseParses.value_unique
  rejectOutputUnique := OptionalWhereClauseRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
