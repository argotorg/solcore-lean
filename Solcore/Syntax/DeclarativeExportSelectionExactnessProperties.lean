import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeExportNameExactnessProperties
import Solcore.Syntax.DeclarativeExportSelectionOutcomeProperties

/-! Exact wildcard or source-order braced remote export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exportSelection_token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (present : TokenAt input.tokens input.endIndex input.cursor
      { span, value := kind })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent ⟨span, present⟩

/-- Remote export selections fix their wildcard span or full braced list. -/
theorem ExportSelectionOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ExportSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ExportSelectionOrdinaryParses input right afterRight) :
    left = right := by
  have itemsOutcomes := trailingDelimitedListExactOutcomeSpec .leftBrace
    .rightBrace exportNameExactOutcomeSpec
  cases leftParsed <;> cases rightParsed <;>
    grind [exportSelection_token_conflicts_absent, TokenAt.token_unique,
      itemsOutcomes.successValueUnique]

/-- Remote export-selection success fixes its complete AST and remainder. -/
theorem ExportSelectionOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ExportSelection}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportSelectionOrdinaryParses input left afterLeft)
    (rightParsed : ExportSelectionOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Remote export-selection rejection fixes its braced-list endpoint. -/
theorem ExportSelectionRejects.output_unique {input left right : Remainder}
    (leftRejected : ExportSelectionRejects input left)
    (rightRejected : ExportSelectionRejects input right) : left = right := by
  cases leftRejected with
  | selectedRejected leftAbsent leftItems =>
      cases rightRejected with
      | selectedRejected rightAbsent rightItems =>
          exact (trailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
            exportNameExactOutcomeSpec).rejectOutputUnique leftItems rightItems

/-- Remote export selections have unconditional exact ordinary outcomes. -/
theorem exportSelectionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExportSelectionOrdinaryParses
      ExportSelectionRejects where
  toDeterministicOutcomeSpec := exportSelectionDeterministicOutcomeSpec
  successValueUnique := ExportSelectionOrdinaryParses.value_unique
  rejectOutputUnique := ExportSelectionRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
