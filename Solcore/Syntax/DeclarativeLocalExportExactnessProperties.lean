import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties
import Solcore.Syntax.DeclarativeFinishExportExactnessProperties
import Solcore.Syntax.DeclarativeLocalExportItemExactnessProperties
import Solcore.Syntax.DeclarativeLocalExportOutcomeProperties

/-! Exact source-order local export payloads at a fixed declaration start. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A local export fixes its entire item list and semicolon-covered AST. -/
theorem LocalExportOrdinaryParses.value_unique {start : SourceSpan}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportOrdinaryParses start input left afterLeft)
    (rightParsed : LocalExportOrdinaryParses start input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftItems, leftAfterItems, leftList, leftFinish⟩
  rcases rightParsed with ⟨rightItems, rightAfterItems, rightList, rightFinish⟩
  rcases (trailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
    localExportItemExactOutcomeSpec).successResultUnique leftList rightList with
    ⟨itemsEq, afterEq⟩
  cases itemsEq
  cases afterEq
  exact (leftFinish.result_unique rightFinish).1

/-- Local export success fixes its entire declaration AST and remainder. -/
theorem LocalExportOrdinaryParses.result_unique {start : SourceSpan}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportOrdinaryParses start input left afterLeft)
    (rightParsed : LocalExportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    LocalExportOrdinaryParses.output_unique start leftParsed rightParsed⟩

/-- Local export rejection fixes the list or finishing endpoint. -/
theorem LocalExportRejects.output_unique {input left right : Remainder}
    (leftRejected : LocalExportRejects input left)
    (rightRejected : LocalExportRejects input right) : left = right := by
  have itemsOutcomes := trailingDelimitedListExactOutcomeSpec .leftBrace
    .rightBrace localExportItemExactOutcomeSpec
  cases leftRejected <;> cases rightRejected <;>
    grind [itemsOutcomes.successOutputUnique, itemsOutcomes.successRejectDisjoint,
      itemsOutcomes.rejectOutputUnique, FinishExportRejects.output_unique]

/-- Local export payloads have unconditional exact outcomes at a shared start. -/
theorem localExportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (LocalExportOrdinaryParses start)
      LocalExportRejects where
  toDeterministicOutcomeSpec := localExportDeterministicOutcomeSpec start
  successValueUnique := LocalExportOrdinaryParses.value_unique
  rejectOutputUnique := LocalExportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
