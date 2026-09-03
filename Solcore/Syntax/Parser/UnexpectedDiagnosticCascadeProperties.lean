import Solcore.Syntax.DeclarativeDiagnosticCascadeProperties
import Solcore.Syntax.Parser.DiagnosticFilter

/-! Exact lexical-cascade filtering of expectation failures with fixed found
token, expected alternatives, and grammar context. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Interpret ordered spans as failures carrying one fixed expectation report. -/
def unexpectedDiagnostics (found : Option TokenKind)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (spans : List SourceSpan) : List ParseDiagnostic :=
  spans.map fun span => { span, kind := .unexpected found expected context }

/-- Interpreting expectation-event spans does not lose their order or identity. -/
@[simp] theorem unexpectedDiagnostics_spans (found : Option TokenKind)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (spans : List SourceSpan) :
    (unexpectedDiagnostics found expected context spans).map ParseDiagnostic.span = spans := by
  simp [unexpectedDiagnostics, List.map_map, Function.comp_def]

/-- Independent keep/drop decisions fix the complete filtered expectation trace. -/
theorem filterParseDiagnostics_unexpected_of_filters
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) {raw kept : List SourceSpan}
    (filtered : DeclarativeGrammar.LexicalCascadeFilters
      file.content (lexical.map (·.span)) raw kept) :
    filterParseDiagnostics file lexical (unexpectedDiagnostics found expected context raw) =
      unexpectedDiagnostics found expected context kept := by
  induction filtered with
  | nil => simp [unexpectedDiagnostics]
  | keep retained tail ih =>
      simp only [unexpectedDiagnostics, List.map_cons] at ih ⊢
      rw [filterParseDiagnostics_cons_unexpected_of_retained _ _ _ _ _ _ _ retained, ih]
  | drop suppressed tail ih =>
      simp only [unexpectedDiagnostics, List.map_cons] at ih ⊢
      rw [filterParseDiagnostics_cons_unexpected_of_suppressed _ _ _ _ _ _ _ suppressed, ih]

/-- Normalization and independent filtering agree with all expectation metadata
shared explicitly; diagnostics are not identified solely by their spans. -/
theorem filterParseDiagnostics_unexpected_iff
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (found : Option TokenKind) (expected : NonemptyList ParseExpectation)
    (context : ParseContext) (raw kept : List SourceSpan) :
    DeclarativeGrammar.LexicalCascadeFilters
      file.content (lexical.map (·.span)) raw kept ↔
      filterParseDiagnostics file lexical (unexpectedDiagnostics found expected context raw) =
        unexpectedDiagnostics found expected context kept := by
  constructor
  · exact filterParseDiagnostics_unexpected_of_filters file lexical found expected context
  · intro result
    rcases DeclarativeGrammar.lexicalCascadeFilters_total
        file.content (lexical.map (·.span)) raw with ⟨actual, filtered⟩
    have reportsEq :=
      (filterParseDiagnostics_unexpected_of_filters file lexical found expected context
        filtered).symm.trans result
    have spansEq := congrArg (List.map ParseDiagnostic.span) reportsEq
    simp only [unexpectedDiagnostics_spans] at spansEq
    simpa only [spansEq] using filtered

end Solcore.Syntax.Parser
