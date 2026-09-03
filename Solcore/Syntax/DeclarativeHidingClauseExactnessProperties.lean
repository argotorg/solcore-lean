import Solcore.Syntax.DeclarativeHidingClauseOutcomeProperties
import Solcore.Syntax.DeclarativeSelectorNameExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties

/-! Exact hiding-clause lists, covered ranges, and optional-clause outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem hiding_marker_present {input output : Remainder}
    {clause : Syntax.HidingClause}
    (parsed : HidingClauseOrdinaryParses input clause output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor
      {span, value := .identifier ContextualKeyword.hiding.spelling} := by
  rcases parsed with ⟨markerSpan, _, markerToken, _⟩
  exact ⟨markerSpan, markerToken⟩

/-- Hiding-clause success fixes its nonempty names and marker-to-list span. -/
theorem HidingClauseOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.HidingClause}
    (leftParsed : HidingClauseOrdinaryParses input left afterLeft)
    (rightParsed : HidingClauseOrdinaryParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftMarkerSpan, leftListSpan, leftMarker, leftNamesParsed, leftSpan⟩
  rcases rightParsed with ⟨rightMarkerSpan, rightListSpan, rightMarker, rightNamesParsed, rightSpan⟩
  have markerEq := leftMarker.token_unique rightMarker
  have namesEq := NonemptyTrailingDelimitedListParses.value_unique
    selectorNameExactOutcomeSpec leftNamesParsed rightNamesParsed
  cases left with
  | mk _ leftValue =>
      cases leftValue with
      | mk leftNames =>
          cases leftNames
          cases right with
          | mk _ rightValue =>
              cases rightValue with
              | mk rightNames =>
                  cases rightNames
                  simp_all [Syntax.NonemptyList.toList]

/-- Required hiding clauses have one complete successful result. -/
theorem HidingClauseOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.HidingClause}
    (leftParsed : HidingClauseOrdinaryParses input left afterLeft)
    (rightParsed : HidingClauseOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Required hiding-clause rejection fixes its first failing endpoint. -/
theorem HidingClauseRejects.output_unique {input left right : Remainder}
    (leftRejected : HidingClauseRejects input left)
    (rightRejected : HidingClauseRejects input right) : left = right := by
  have listExact := nonemptyTrailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
    selectorNameExactOutcomeSpec
  cases leftRejected <;> cases rightRejected <;>
    grind [absent_conflicts_exact, ExactTokenParses.output_unique,
      listExact.rejectOutputUnique]

/-- Required hiding clauses have fully functional success and rejection. -/
theorem hidingClauseExactOutcomeSpec :
    ExactDeterministicOutcomeSpec HidingClauseOrdinaryParses HidingClauseRejects where
  toDeterministicOutcomeSpec := hidingClauseDeterministicOutcomeSpec
  successValueUnique := HidingClauseOrdinaryParses.value_unique
  rejectOutputUnique := HidingClauseRejects.output_unique

/-- Maximal optional hiding fixes both clause presence and the located AST. -/
theorem OptionalHidingOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.HidingClause}
    (leftParsed : OptionalHidingOrdinaryParses input left afterLeft)
    (rightParsed : OptionalHidingOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightClause => exact False.elim (leftAbsent (hiding_marker_present rightClause))
  | present leftClause =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent (hiding_marker_present leftClause))
      | present rightClause =>
          exact congrArg some (hidingClauseExactOutcomeSpec.successValueUnique
            leftClause rightClause)

/-- Optional hiding fixes the complete successful result. -/
theorem OptionalHidingOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Option Syntax.HidingClause}
    (leftParsed : OptionalHidingOrdinaryParses input left afterLeft)
    (rightParsed : OptionalHidingOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Optional hiding rejection inherits the required clause's exact endpoint. -/
theorem OptionalHidingRejects.output_unique {input left right : Remainder}
    (leftRejected : OptionalHidingRejects input left)
    (rightRejected : OptionalHidingRejects input right) : left = right := by
  cases leftRejected with
  | present _ leftClause =>
      cases rightRejected with
      | present _ rightClause => exact leftClause.output_unique rightClause

/-- Optional hiding has fully functional success and rejection outcomes. -/
theorem optionalHidingExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalHidingOrdinaryParses OptionalHidingRejects where
  toDeterministicOutcomeSpec := optionalHidingDeterministicOutcomeSpec
  successValueUnique := OptionalHidingOrdinaryParses.value_unique
  rejectOutputUnique := OptionalHidingRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
