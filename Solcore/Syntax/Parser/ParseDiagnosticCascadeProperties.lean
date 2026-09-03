import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.DiagnosticFilter

/-! Exact independent normalization of arbitrary mixed parser diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Independent normalization determines each retained complete diagnostic. -/
theorem filterParseDiagnostics_eq_of_cascadeFilters
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    {raw kept : List ParseDiagnostic}
    (filtered : DeclarativeGrammar.ParseDiagnosticCascadeFilters
      file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical raw = kept := by
  induction filtered with
  | nil => exact filterParseDiagnostics_nil_parsed file lexical
  | keep retained tail ih =>
      rw [filterParseDiagnostics_cons_of_retained _ _ _ _ retained, ih]
  | drop suppressed tail ih =>
      rw [filterParseDiagnostics_cons_of_suppressed _ _ _ _ suppressed, ih]

/-- The filter is exactly the independent mixed-report relation, not merely a
span projection. Expectations, contexts, text, and constraint payloads remain exact. -/
theorem filterParseDiagnostics_eq_iff_cascadeFilters
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (raw kept : List ParseDiagnostic) :
    filterParseDiagnostics file lexical raw = kept ↔
      DeclarativeGrammar.ParseDiagnosticCascadeFilters
        file.content (lexical.map (·.span)) raw kept := by
  constructor
  · intro result
    rcases DeclarativeGrammar.parseDiagnosticCascadeFilters_total
        file.content (lexical.map (·.span)) raw with ⟨actual, filtered⟩
    have actualEq := (filterParseDiagnostics_eq_of_cascadeFilters file lexical filtered).symm.trans result
    simpa only [actualEq] using filtered
  · exact filterParseDiagnostics_eq_of_cascadeFilters file lexical

end Solcore.Syntax.Parser
