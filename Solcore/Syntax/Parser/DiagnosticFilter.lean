import Solcore.Syntax.Parser.SourceFiles
import Solcore.Syntax.Parser.Trivia
import Solcore.Syntax.Grammar.Basics

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Suppression of a complete diagnostic preserves the untouched suffix. -/
theorem filterParseDiagnostics_cons_of_suppressed
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (diagnostic : ParseDiagnostic) (parsed : List ParseDiagnostic)
    (suppressed : DeclarativeGrammar.ParseDiagnosticCascadeSuppresses
      file.content (lexical.map (·.span)) diagnostic) :
    filterParseDiagnostics file lexical (diagnostic :: parsed) =
      filterParseDiagnostics file lexical parsed := by
  rcases diagnostic with ⟨span, kind⟩
  cases kind with
  | unexpected found expected context =>
      exact filterParseDiagnostics_cons_unexpected_of_suppressed
        file lexical span found expected context parsed suppressed.2
  | recovered site =>
      exact filterParseDiagnostics_cons_recovered_of_suppressed
        file lexical span site parsed suppressed.2
  | invalidIdentifierHyphen text => exact False.elim suppressed.1
  | constraintViolation constraint => exact False.elim suppressed.1
  | nestingExceeded kind limit => exact False.elim suppressed.1

/-- Filtering lexical cascades preserves validity of every retained span. -/
theorem filterParseDiagnostics_spans_validFor
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic)
    (valid : ∀ diagnostic ∈ parsed, diagnostic.span.ValidFor file) :
    ∀ diagnostic ∈ filterParseDiagnostics file lexical parsed,
      diagnostic.span.ValidFor file := by
  intro diagnostic member
  exact valid diagnostic
    (mem_of_mem_filterParseDiagnostics file lexical parsed diagnostic member)

end Solcore.Syntax.Parser
