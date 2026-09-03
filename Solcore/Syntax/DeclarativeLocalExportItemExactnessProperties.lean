import Solcore.Syntax.DeclarativeExportNameExactnessProperties
import Solcore.Syntax.DeclarativeExportPathExactnessProperties
import Solcore.Syntax.DeclarativeLocalExportItemOutcomeProperties

/-! Exact local export names and qualified module wildcards. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem localExport_initial_dot
    {tokens : Array Token} {endIndex cursor finish : Nat}
    {components : List Syntax.Identifier} {dotSpan : SourceSpan}
    (tail : ExportPathTailParses tokens endIndex cursor components finish)
    (dot : TokenAt tokens endIndex finish
      { span := dotSpan, value := .symbol .dot }) :
    ∃ span, TokenAt tokens endIndex cursor
      { span, value := .symbol .dot } := by
  cases tail with
  | done cursor stopped => exact ⟨dotSpan, dot⟩
  | next initialSpan initialDot component rest => exact ⟨initialSpan, initialDot⟩

private theorem localExport_qualified_of_path_dot
    {input afterPath : Remainder} {path : Syntax.QualifiedName}
    {dotSpan : SourceSpan}
    (parsed : ExportPathParses input path afterPath)
    (dot : TokenAt afterPath.tokens afterPath.endIndex afterPath.cursor
      { span := dotSpan, value := .symbol .dot }) :
    LocalExportItemQualifiedStartAt input := by
  rcases parsed with ⟨tokensEq, endIndexEq, first, tail, spanEq⟩
  have finishDot : TokenAt input.tokens input.endIndex afterPath.cursor
      { span := dotSpan, value := .symbol .dot } := by
    simpa only [tokensEq, endIndexEq] using dot
  obtain ⟨initialSpan, initialDot⟩ := localExport_initial_dot tail finishDot
  exact ⟨_, initialSpan, _, first, initialDot⟩

private theorem localExport_qualified_conflicts_absent {input : Remainder}
    (present : LocalExportItemQualifiedStartAt input)
    (absent : IdentifierDotAbsentAt input.tokens input.endIndex input.cursor) :
    False :=
  absent present

private theorem localExport_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Local export items fix the complete path, wildcard marker, or name AST. -/
theorem LocalExportItemOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.LocalExportItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportItemOrdinaryParses input left afterLeft)
    (rightParsed : LocalExportItemOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [→ localExport_qualified_of_path_dot,
      localExport_qualified_conflicts_absent,
      exportPathExactOutcomeSpec.successResultUnique,
      exportNameExactOutcomeSpec.successValueUnique, TokenAt.token_unique]

/-- Local export-item success fixes its complete AST and final remainder. -/
theorem LocalExportItemOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.LocalExportItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportItemOrdinaryParses input left afterLeft)
    (rightParsed : LocalExportItemOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Local export-item rejection fixes its selected path or name endpoint. -/
theorem LocalExportItemRejects.output_unique {input left right : Remainder}
    (leftRejected : LocalExportItemRejects input left)
    (rightRejected : LocalExportItemRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [localExport_qualified_conflicts_absent,
      localExport_absent_conflicts_exact,
      exportPathExactOutcomeSpec.successOutputUnique,
      exportNameExactOutcomeSpec.rejectOutputUnique,
      ExactTokenParses.output_unique]

/-- Local export items have unconditional exact ordinary outcomes. -/
theorem localExportItemExactOutcomeSpec :
    ExactDeterministicOutcomeSpec LocalExportItemOrdinaryParses
      LocalExportItemRejects where
  toDeterministicOutcomeSpec := localExportItemDeterministicOutcomeSpec
  successValueUnique := LocalExportItemOrdinaryParses.value_unique
  rejectOutputUnique := LocalExportItemRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
