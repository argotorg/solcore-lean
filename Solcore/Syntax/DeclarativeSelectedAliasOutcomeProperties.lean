import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectedAliasOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for selected-import aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Ordinary selected aliases have one final remainder. -/
theorem SelectedAliasOrdinaryParses.output_unique
    {input : Remainder} {left right : Option Syntax.Identifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : SelectedAliasOrdinaryParses input left afterLeft)
    (rightParsed : SelectedAliasOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present markerSpan markerToken nameToken tokensEq endIndexEq cursorEq =>
          exact False.elim
            (absent_conflicts_token leftAbsent markerToken)
  | present markerSpan markerToken nameToken tokensEq endIndexEq cursorEq =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (absent_conflicts_token rightAbsent markerToken)
      | present rightMarkerSpan rightMarkerToken rightNameToken rightTokensEq
          rightEndIndexEq rightCursorEq =>
          cases input
          cases afterLeft
          cases afterRight
          simp_all

/-- Selected-alias rejection stops immediately after the committed `as`. -/
theorem SelectedAliasRejects.output_eq {input rejected : Remainder}
    (rejection : SelectedAliasRejects input rejected) :
    rejected = { input with cursor := input.cursor + 1 } := by
  cases rejection with
  | nameRejected markerSpan markerParsed nameRejected =>
      cases nameRejected
      exact markerParsed.2

/-- Exact selected-alias rejection excludes absent and present success. -/
theorem SelectedAliasRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : SelectedAliasRejects input rejected) :
    ¬ ∃ alias output,
      SelectedAliasOrdinaryParses input alias output := by
  rintro ⟨alias, output, successful⟩
  cases rejection with
  | nameRejected markerSpan markerParsed nameRejected =>
      cases successful with
      | absent markerAbsent =>
          exact absent_conflicts_token markerAbsent markerParsed.1
      | present successfulMarkerSpan successfulMarker nameToken tokensEq
          endIndexEq cursorEq =>
          cases nameRejected with
          | absent identifierAbsent =>
              rw [markerParsed.2] at identifierAbsent
              exact identifierAbsent ⟨_, _, by simpa using nameToken⟩

/-- Selected-import aliases have deterministic and exclusive broad ordinary
outcomes. -/
theorem selectedAliasDeterministicOutcomeSpec :
    DeterministicOutcomeSpec SelectedAliasOrdinaryParses
      SelectedAliasRejects where
  successOutputUnique := SelectedAliasOrdinaryParses.output_unique
  successRejectDisjoint := SelectedAliasRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
