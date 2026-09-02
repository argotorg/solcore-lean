import Solcore.Syntax.DeclarativeFileItemsOutcomeProperties
import Solcore.Syntax.DeclarativeSourceFileOutcomeGrammar

/-! Deterministic broad ordinary outcomes for complete syntax files. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recovery-aware complete-file success has one final remainder. -/
theorem SourceFileOrdinaryParses.output_unique
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input : Remainder} {left right : Syntax.ParsedFile}
    {afterLeft afterRight : Remainder}
    (leftParsed : SourceFileOrdinaryParses file comments input left afterLeft)
    (rightParsed : SourceFileOrdinaryParses file comments input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftItems =>
      cases rightParsed with
      | parsed rightItems => exact leftItems.output_unique rightItems

/-- Exact complete-file rejection excludes every broad ordinary success. -/
theorem SourceFileRejects.disjointOrdinary
    {file : Syntax.SourceFile} {comments : List Syntax.Comment}
    {input rejected : Remainder} (rejection : SourceFileRejects input rejected) :
    ¬ ∃ parsedFile output,
      SourceFileOrdinaryParses file comments input parsedFile output := by
  rintro ⟨parsedFile, output, parsed⟩
  cases rejection with
  | itemsRejected itemsRejected =>
      cases parsed with
      | parsed itemsParsed =>
          exact itemsRejected.disjointOrdinary ⟨_, _, itemsParsed⟩

/-- Complete source files have deterministic and exclusive broad outcomes. -/
theorem sourceFileDeterministicOutcomeSpec
    (file : Syntax.SourceFile) (comments : List Syntax.Comment) :
    DeterministicOutcomeSpec (SourceFileOrdinaryParses file comments)
      SourceFileRejects where
  successOutputUnique := SourceFileOrdinaryParses.output_unique
  successRejectDisjoint := SourceFileRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
