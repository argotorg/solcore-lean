import Solcore.Syntax.DeclarativeExportPathExactnessProperties
import Solcore.Syntax.DeclarativeExportSelectionExactnessProperties
import Solcore.Syntax.DeclarativeFinishExportExactnessProperties
import Solcore.Syntax.DeclarativePathExportOutcomeProperties

/-! Exact module, alias, and selected path export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem pathExport_token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (present : TokenAt input.tokens input.endIndex input.cursor
      { span, value := kind })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent ⟨span, present⟩

private theorem pathExport_present_conflicts_absent {input : Remainder}
    {kind : TokenKind} (present : PathExportTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent present

/-- Path export payloads fix their paths, suffixes, and semicolon-covered AST
at a shared outer declaration start. -/
theorem PathExportOrdinaryParses.value_unique {start : SourceSpan}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PathExportOrdinaryParses start input left afterLeft)
    (rightParsed : PathExportOrdinaryParses start input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [ItemsFromExportTailParses, ModuleAsExportTailParses,
      ModuleExportTailParses, pathExport_token_conflicts_absent,
      exportPathExactOutcomeSpec.successResultUnique,
      exportSelectionExactOutcomeSpec.successResultUnique,
      identifierExactOutcomeSpec.successResultUnique,
      FinishExportParses.result_unique]

/-- Path export success fixes its complete declaration AST and remainder. -/
theorem PathExportOrdinaryParses.result_unique {start : SourceSpan}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : PathExportOrdinaryParses start input left afterLeft)
    (rightParsed : PathExportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    PathExportOrdinaryParses.output_unique start leftParsed rightParsed⟩

/-- Path export rejection fixes its first priority-selected failing endpoint. -/
theorem PathExportRejects.output_unique {input left right : Remainder}
    (leftRejected : PathExportRejects input left)
    (rightRejected : PathExportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [pathExport_present_conflicts_absent, ExactTokenParses.output_unique,
      exportPathExactOutcomeSpec.successOutputUnique,
      exportPathExactOutcomeSpec.successRejectDisjoint,
      exportPathExactOutcomeSpec.rejectOutputUnique,
      exportSelectionExactOutcomeSpec.successOutputUnique,
      exportSelectionExactOutcomeSpec.successRejectDisjoint,
      exportSelectionExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      FinishExportRejects.output_unique]

/-- Path export payloads have unconditional exact outcomes at a shared start. -/
theorem pathExportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (PathExportOrdinaryParses start)
      PathExportRejects where
  toDeterministicOutcomeSpec := pathExportDeterministicOutcomeSpec start
  successValueUnique := PathExportOrdinaryParses.value_unique
  rejectOutputUnique := PathExportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
