import Solcore.Syntax.DeclarativeImplDefaultMarkerOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Deterministic exact outcomes for the optional implementation marker. -/

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

/-- Optional implementation markers have one final remainder. -/
theorem OptionalImplDefaultMarkerOrdinaryParses.output_unique
    {input : Remainder} {left right : Option SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalImplDefaultMarkerOrdinaryParses input left afterLeft)
    (rightParsed : OptionalImplDefaultMarkerOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightMarker =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftSpan leftMarker =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightSpan rightMarker =>
          exact exactToken_output_unique leftMarker rightMarker

/-- The impossible reject relation is disjoint from every ordinary success. -/
theorem OptionalImplDefaultMarkerRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalImplDefaultMarkerRejects input rejected) :
    ¬ ∃ marker output,
      OptionalImplDefaultMarkerOrdinaryParses input marker output := by
  exact False.elim rejection

/-- Optional implementation markers have deterministic ordinary outcomes and
cannot reject. -/
theorem optionalImplDefaultMarkerDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalImplDefaultMarkerOrdinaryParses
      OptionalImplDefaultMarkerRejects where
  successOutputUnique :=
    OptionalImplDefaultMarkerOrdinaryParses.output_unique
  successRejectDisjoint :=
    OptionalImplDefaultMarkerRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
