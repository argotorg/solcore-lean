import Solcore.Syntax.DeclarativeCoreBlockTailTraceProperties

/-! Independent normalization of statement events followed by tail validation.
Only the leading events may be filtered; the complete protected tail stays last. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Filtering arbitrary earlier events preserves the complete appended tail
trace, including its original order, full reports, and duplicate occurrences. -/
theorem CoreBlockTailsDiagnosticTrace.append_cascadeFilters
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {tailTrace events keptEvents : List ParseDiagnostic}
    {text : String} {lexical : List SourceSpan}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements tailTrace)
    (filtered : ParseDiagnosticCascadeFilters text lexical events keptEvents) :
    ParseDiagnosticCascadeFilters text lexical
      (events ++ tailTrace) (keptEvents ++ tailTrace) :=
  filtered.append (parsed.cascadeFilters text lexical)

/-- Every possible normalized result is exactly a normalized event prefix
followed by the unchanged tail-validation trace; the converse also holds. -/
theorem CoreBlockTailsDiagnosticTrace.append_cascadeFilters_iff
    {policy : CoreBlockTailPolicy} {statements : List Syntax.Statement}
    {tailTrace events kept : List ParseDiagnostic}
    (parsed : CoreBlockTailsDiagnosticTrace policy statements tailTrace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical (events ++ tailTrace) kept ↔
      ∃ keptEvents, ParseDiagnosticCascadeFilters text lexical events keptEvents ∧
        kept = keptEvents ++ tailTrace := by
  constructor
  · intro filtered
    rcases parseDiagnosticCascadeFilters_total text lexical events with ⟨keptEvents, leading⟩
    exact ⟨keptEvents, leading,
      filtered.output_unique (parsed.append_cascadeFilters leading)⟩
  · rintro ⟨keptEvents, leading, rfl⟩
    exact parsed.append_cascadeFilters leading

end Solcore.Syntax.DeclarativeGrammar
