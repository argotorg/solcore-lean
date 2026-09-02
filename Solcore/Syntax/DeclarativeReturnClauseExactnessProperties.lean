import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeReturnClauseOutcomeProperties

/-! Full value and rejection-endpoint functionality for optional returns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem return_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem returnTypeListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftParen .rightParen TypeExprParses)
      (DelimitedListRejects .leftParen .rightParen true true TypeExprParses
        TypeExprRejects) :=
  trailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    typeExprExactOutcomeSpec

/-- An optional return clause fixes its absent or present AST value. -/
theorem OptionalReturnClauseParses.value_unique
    {input : Remainder} {left right : Option Syntax.ReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnClauseParses input left afterLeft)
    (rightParsed : OptionalReturnClauseParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightMarkerSpan rightMarker rightTypes =>
          exact False.elim
            (return_absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftTypes =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (return_absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightTypes =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          have typesEq := returnTypeListExactOutcomeSpec.successValueUnique
            leftTypes rightTypes
          subst typesEq
          rfl

/-- An optional return clause fixes its value and final remainder. -/
theorem OptionalReturnClauseParses.result_unique
    {input : Remainder} {left right : Option Syntax.ReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnClauseParses input left afterLeft)
    (rightParsed : OptionalReturnClauseParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A committed return-clause rejection has one failing endpoint. -/
theorem OptionalReturnClauseRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalReturnClauseRejects input left)
    (rightRejected : OptionalReturnClauseRejects input right) : left = right := by
  cases leftRejected with
  | typesRejected _ leftMarker leftTypes =>
      cases rightRejected with
      | typesRejected _ rightMarker rightTypes =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          exact returnTypeListExactOutcomeSpec.rejectOutputUnique leftTypes
            rightTypes

/-- Optional return clauses have fully exact ordinary outcomes. -/
theorem optionalReturnClauseExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalReturnClauseParses
      OptionalReturnClauseRejects where
  toDeterministicOutcomeSpec := optionalReturnClauseDeterministicOutcomeSpec
  successValueUnique := OptionalReturnClauseParses.value_unique
  rejectOutputUnique := OptionalReturnClauseRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
