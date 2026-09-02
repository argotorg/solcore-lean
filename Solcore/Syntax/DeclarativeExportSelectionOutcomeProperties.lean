import Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeExportNameOutcomeProperties
import Solcore.Syntax.DeclarativeExportSelectionOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (token : TokenAt input.tokens input.endIndex input.cursor {
      span
      value := kind
    })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      kind) : False :=
  absent ⟨span, token⟩

private theorem exportSelectionItemsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftBrace .rightBrace
        ExportNameOrdinaryParses)
      (DelimitedListRejects .leftBrace .rightBrace true true
        ExportNameOrdinaryParses ExportNameRejects) :=
  trailingDelimitedListDeterministicOutcomeSpec .leftBrace .rightBrace
    exportNameDeterministicOutcomeSpec

/-- Prioritized export-selection success has one final remainder. -/
theorem ExportSelectionOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ExportSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ExportSelectionOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | wildcard leftSpan leftMarker =>
      cases rightParsed with
      | wildcard => rfl
      | selected rightStar rightItems =>
          exact False.elim (token_conflicts_absent leftMarker rightStar)
  | selected leftStar leftItems =>
      cases rightParsed with
      | wildcard rightSpan rightMarker =>
          exact False.elim (token_conflicts_absent rightMarker leftStar)
      | selected rightStar rightItems =>
          exact exportSelectionItemsDeterministicOutcomeSpec
            |>.successOutputUnique leftItems rightItems

/-- Exact selected-branch rejection excludes ordinary export-selection
success. -/
theorem ExportSelectionRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ExportSelectionRejects input rejected) :
    ¬ ∃ selection output,
      ExportSelectionOrdinaryParses input selection output := by
  rintro ⟨selection, output, successful⟩
  cases rejection with
  | selectedRejected starAbsent itemsRejected =>
      cases successful with
      | wildcard markerSpan markerToken =>
          exact token_conflicts_absent markerToken starAbsent
      | selected successfulStar itemsParsed =>
          exact exportSelectionItemsDeterministicOutcomeSpec
            |>.successRejectDisjoint itemsRejected ⟨_, _, itemsParsed⟩

/-- Export selections have deterministic and exclusive broad outcomes. -/
theorem exportSelectionDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ExportSelectionOrdinaryParses
      ExportSelectionRejects where
  successOutputUnique := ExportSelectionOrdinaryParses.output_unique
  successRejectDisjoint := ExportSelectionRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
