import Solcore.Syntax.DeclarativeImplDefaultMarkerOutcomeProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact outcomes for the optional leading `default` implementation marker. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem implDefault_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- The optional implementation marker fixes its absent or present span. -/
theorem OptionalImplDefaultMarkerOrdinaryParses.value_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalImplDefaultMarkerOrdinaryParses input left afterLeft)
    (rightParsed : OptionalImplDefaultMarkerOrdinaryParses input right
      afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightMarker =>
          exact False.elim
            (implDefault_absent_conflicts_exact leftAbsent rightMarker)
  | present leftSpan leftMarker =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (implDefault_absent_conflicts_exact rightAbsent leftMarker)
      | present rightSpan rightMarker =>
          rw [leftMarker.span_unique rightMarker]

/-- The optional implementation marker fixes its value and final remainder. -/
theorem OptionalImplDefaultMarkerOrdinaryParses.result_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalImplDefaultMarkerOrdinaryParses input left afterLeft)
    (rightParsed : OptionalImplDefaultMarkerOrdinaryParses input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The impossible optional-marker rejection has a unique endpoint. -/
theorem OptionalImplDefaultMarkerRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalImplDefaultMarkerRejects input left)
    (_rightRejected : OptionalImplDefaultMarkerRejects input right) :
    left = right :=
  False.elim leftRejected

/-- Optional implementation markers have fully exact outcomes. -/
theorem optionalImplDefaultMarkerExactOutcomeSpec :
    ExactDeterministicOutcomeSpec OptionalImplDefaultMarkerOrdinaryParses
      OptionalImplDefaultMarkerRejects where
  toDeterministicOutcomeSpec :=
    optionalImplDefaultMarkerDeterministicOutcomeSpec
  successValueUnique := OptionalImplDefaultMarkerOrdinaryParses.value_unique
  rejectOutputUnique := OptionalImplDefaultMarkerRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
