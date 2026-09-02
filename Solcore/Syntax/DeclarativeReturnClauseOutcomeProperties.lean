import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeReturnClauseOutcomeGrammar

/-! Deterministic exact outcomes for optional canonical `returns` clauses. -/

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

private theorem returnTypeListDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftParen .rightParen
        TypeExprOrdinaryParses)
      (DelimitedListRejects .leftParen .rightParen true true
        TypeExprOrdinaryParses TypeExprRejects) :=
  trailingDelimitedListDeterministicOutcomeSpec .leftParen .rightParen
    typeExprDeterministicOutcomeSpec

/-- Optional `returns` success has one final remainder. -/
theorem OptionalReturnClauseParses.output_unique
    {input : Remainder} {left right : Option Syntax.ReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnClauseParses input left afterLeft)
    (rightParsed : OptionalReturnClauseParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightMarkerSpan rightMarker rightTypes =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | present leftMarkerSpan leftMarker leftTypes =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | present rightMarkerSpan rightMarker rightTypes =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact returnTypeListDeterministicOutcomeSpec.successOutputUnique
            leftTypes rightTypes

/-- Exact optional-`returns` rejection excludes every successful branch. -/
theorem OptionalReturnClauseRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalReturnClauseRejects input rejected) :
    ¬ ∃ clause output, OptionalReturnClauseParses input clause output := by
  rintro ⟨clause, output, successful⟩
  cases rejection with
  | typesRejected rejectedMarkerSpan rejectedMarker typesRejected =>
      cases successful with
      | absent markerAbsent =>
          exact absent_conflicts_exact markerAbsent rejectedMarker
      | present successfulMarkerSpan successfulMarker typesParsed =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact returnTypeListDeterministicOutcomeSpec.successRejectDisjoint
            typesRejected ⟨_, _, typesParsed⟩

/-- Optional canonical `returns` has deterministic and exclusive outcomes. -/
theorem optionalReturnClauseDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalReturnClauseParses
      OptionalReturnClauseRejects where
  successOutputUnique := OptionalReturnClauseParses.output_unique
  successRejectDisjoint := OptionalReturnClauseRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
