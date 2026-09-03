import Solcore.Syntax.DeclarativeFileItemsExactnessProperties
import Solcore.Syntax.DeclarativeSourceFileOutcomeProperties

/-! Exact source-file outcomes through deterministic source-order trivia attachment. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact raw items fix the complete source-file AST after pure comment attachment. -/
theorem SourceFileOrdinaryParses.value_unique_of_fileItems
    (itemsOutcomes : ExactDeterministicOutcomeSpec FileItemsOrdinaryParses
      FileItemsRejects)
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input : Remainder} {left right : Syntax.ParsedFile}
    {afterLeft afterRight : Remainder}
    (leftParsed : SourceFileOrdinaryParses file comments input left afterLeft)
    (rightParsed : SourceFileOrdinaryParses file comments input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftItems =>
      cases rightParsed with
      | parsed rightItems =>
          have itemsEq := itemsOutcomes.successValueUnique leftItems rightItems
          subst itemsEq
          rfl

/-- Exact raw items fix both the source-file AST and the grammar's final remainder. -/
theorem SourceFileOrdinaryParses.result_unique_of_fileItems
    (itemsOutcomes : ExactDeterministicOutcomeSpec FileItemsOrdinaryParses
      FileItemsRejects)
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input : Remainder} {left right : Syntax.ParsedFile}
    {afterLeft afterRight : Remainder}
    (leftParsed : SourceFileOrdinaryParses file comments input left afterLeft)
    (rightParsed : SourceFileOrdinaryParses file comments input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_fileItems itemsOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Source-file rejection has one endpoint without any exact top-item premise. -/
theorem SourceFileRejects.output_unique {input left right : Remainder}
    (leftRejected : SourceFileRejects input left)
    (rightRejected : SourceFileRejects input right) : left = right := by
  cases leftRejected with
  | itemsRejected leftItems =>
      cases rightRejected with
      | itemsRejected rightItems => exact leftItems.output_unique rightItems

/-- Exact raw-item outcomes lift through fixed file provenance and comments. -/
theorem sourceFileExactOutcomeSpecOfFileItems
    (itemsOutcomes : ExactDeterministicOutcomeSpec FileItemsOrdinaryParses
      FileItemsRejects)
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    ExactDeterministicOutcomeSpec (SourceFileOrdinaryParses file comments)
      SourceFileRejects where
  toDeterministicOutcomeSpec := sourceFileDeterministicOutcomeSpec file comments
  successValueUnique :=
    SourceFileOrdinaryParses.value_unique_of_fileItems itemsOutcomes
  rejectOutputUnique := SourceFileRejects.output_unique

/-- Unique top-item success values suffice for complete source-file exactness. -/
theorem sourceFileExactOutcomeSpecOfTopItemValues
    (itemValues : ∀ {input left right afterLeft afterRight},
      TopItemOrdinaryParses input left afterLeft →
      TopItemOrdinaryParses input right afterRight → left = right)
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    ExactDeterministicOutcomeSpec (SourceFileOrdinaryParses file comments)
      SourceFileRejects :=
  sourceFileExactOutcomeSpecOfFileItems
    (fileItemsExactOutcomeSpecOfTopItemValues itemValues) file comments

/-- An exact top-item contract supplies exact recovery-aware source-file outcomes. -/
theorem sourceFileExactOutcomeSpecOfTopItem
    (itemOutcomes : ExactDeterministicOutcomeSpec TopItemOrdinaryParses
      TopItemRejects)
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    ExactDeterministicOutcomeSpec (SourceFileOrdinaryParses file comments)
      SourceFileRejects :=
  sourceFileExactOutcomeSpecOfTopItemValues itemOutcomes.successValueUnique
    file comments

end Solcore.Syntax.DeclarativeGrammar
