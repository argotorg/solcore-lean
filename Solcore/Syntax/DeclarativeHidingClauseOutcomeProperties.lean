import Solcore.Syntax.DeclarativeDelimitedNonemptyTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeHidingClauseOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectorNameOutcomeProperties

/-! Deterministic and exclusive broad ordinary hiding-clause outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span
      value := kind
    }) : False :=
  absent ⟨span, present⟩

private theorem HidingClauseOrdinaryParses.marker_present
    {input output : Remainder} {clause : Syntax.HidingClause}
    (parsed : HidingClauseOrdinaryParses input clause output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .identifier ContextualKeyword.hiding.spelling
    } := by
  unfold HidingClauseOrdinaryParses HidingClauseParses at parsed
  rcases parsed with ⟨markerSpan, listSpan, markerToken, namesParsed,
    spanEq⟩
  exact ⟨markerSpan, markerToken⟩

/-- Ordinary hiding clauses have one final remainder. -/
theorem HidingClauseOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.HidingClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : HidingClauseOrdinaryParses input left afterLeft)
    (rightParsed : HidingClauseOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold HidingClauseOrdinaryParses HidingClauseParses at leftParsed rightParsed
  rcases leftParsed with ⟨leftMarkerSpan, leftListSpan, leftMarker,
    leftNames, leftSpanEq⟩
  rcases rightParsed with ⟨rightMarkerSpan, rightListSpan, rightMarker,
    rightNames, rightSpanEq⟩
  unfold NonemptySelectorListParses at leftNames rightNames
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .leftBrace) (closing := .rightBrace)
    (elementParses := SelectorNameOrdinaryParses)
    SelectorNameOrdinaryParses.output_unique leftNames rightNames

/-- Exact required-clause rejection excludes every ordinary success. -/
theorem HidingClauseRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : HidingClauseRejects input rejected) :
    ¬ ∃ clause output,
      HidingClauseOrdinaryParses input clause output := by
  rintro ⟨clause, output, successful⟩
  cases rejection with
  | markerMissing markerAbsent =>
      rcases successful.marker_present with ⟨span, markerPresent⟩
      exact absent_conflicts_token markerAbsent markerPresent
  | namesRejected markerSpan markerParsed namesRejected =>
      unfold HidingClauseOrdinaryParses HidingClauseParses at successful
      rcases successful with ⟨successfulMarkerSpan, listSpan,
        successfulMarker, namesParsed, spanEq⟩
      rw [markerParsed.2] at namesRejected
      unfold NonemptySelectorListParses at namesParsed
      exact namesRejected.disjointNonemptyTrailing
        selectorNameDeterministicOutcomeSpec (fun parsed => parsed)
        ⟨_, _, namesParsed⟩

/-- Required hiding clauses have deterministic and exclusive broad ordinary
outcomes. -/
theorem hidingClauseDeterministicOutcomeSpec :
    DeterministicOutcomeSpec HidingClauseOrdinaryParses
      HidingClauseRejects where
  successOutputUnique := HidingClauseOrdinaryParses.output_unique
  successRejectDisjoint := HidingClauseRejects.disjointOrdinary

/-- Ordinary optional hiding clauses have one final remainder. -/
theorem OptionalHidingOrdinaryParses.output_unique
    {input : Remainder} {left right : Option Syntax.HidingClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalHidingOrdinaryParses input left afterLeft)
    (rightParsed : OptionalHidingOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightClause =>
          rcases HidingClauseOrdinaryParses.marker_present rightClause with
            ⟨span, markerPresent⟩
          exact False.elim
            (absent_conflicts_token leftAbsent markerPresent)
  | present leftClause =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases HidingClauseOrdinaryParses.marker_present leftClause with
            ⟨span, markerPresent⟩
          exact False.elim
            (absent_conflicts_token rightAbsent markerPresent)
      | present rightClause =>
          exact HidingClauseOrdinaryParses.output_unique leftClause
            rightClause

/-- Guarded optional rejection excludes absent and present ordinary success. -/
theorem OptionalHidingRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalHidingRejects input rejected) :
    ¬ ∃ hidden output,
      OptionalHidingOrdinaryParses input hidden output := by
  rintro ⟨hidden, output, successful⟩
  cases rejection with
  | present markerPresent clauseRejected =>
      cases successful with
      | absent markerAbsent =>
          rcases markerPresent with ⟨span, markerToken⟩
          exact absent_conflicts_token markerAbsent markerToken
      | present clauseParsed =>
          exact hidingClauseDeterministicOutcomeSpec.successRejectDisjoint
            clauseRejected ⟨_, _, clauseParsed⟩

/-- Optional hiding clauses have deterministic and exclusive broad ordinary
outcomes. -/
theorem optionalHidingDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalHidingOrdinaryParses
      OptionalHidingRejects where
  successOutputUnique := OptionalHidingOrdinaryParses.output_unique
  successRejectDisjoint := OptionalHidingRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
