import Solcore.Syntax.DeclarativeDiagnosticCascadeProperties
import Solcore.Syntax.Parser.DiagnosticFilter
import Solcore.Syntax.Parser.TopItemRecoveryTraceCompletenessProperties

/-! Exact correspondence between independent cascade filtering and the public
normalization of top-item recovery event lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open FileInternals

/-- Independent keep/drop decisions determine the complete filtered event list. -/
theorem filterParseDiagnostics_recoveredTopItems_of_filters
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    {raw kept : List SourceSpan}
    (filtered : DeclarativeGrammar.LexicalCascadeFilters
      file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical (topItemRecoveryDiagnostics raw) =
      topItemRecoveryDiagnostics kept := by
  induction filtered with
  | nil => simp [topItemRecoveryDiagnostics]
  | keep retained tail ih =>
      simp only [topItemRecoveryDiagnostics, List.map_cons] at ih ⊢
      rw [filterParseDiagnostics_cons_recovered_of_retained _ _ _ _ _ retained, ih]
  | drop suppressed tail ih =>
      simp only [topItemRecoveryDiagnostics, List.map_cons] at ih ⊢
      rw [filterParseDiagnostics_cons_recovered_of_suppressed _ _ _ _ _ suppressed, ih]

/-- Recovery-event normalization and the independent span-filter relation
agree in both directions, including order and duplicates. -/
theorem filterParseDiagnostics_recoveredTopItems_iff
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List SourceSpan) :
    DeclarativeGrammar.LexicalCascadeFilters
      file.content (lexical.map (·.span)) raw kept ↔
      filterParseDiagnostics file lexical (topItemRecoveryDiagnostics raw) =
        topItemRecoveryDiagnostics kept := by
  constructor
  · exact filterParseDiagnostics_recoveredTopItems_of_filters file lexical
  · intro result
    rcases DeclarativeGrammar.lexicalCascadeFilters_total
        file.content (lexical.map (·.span)) raw with ⟨actual, filtered⟩
    have equal := topItemRecoveryDiagnostics_injective
      ((filterParseDiagnostics_recoveredTopItems_of_filters file lexical filtered).symm.trans
        result)
    simpa only [equal] using filtered

end Solcore.Syntax.Parser
