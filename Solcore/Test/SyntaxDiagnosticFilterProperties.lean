import Solcore

/-! External compile consumers for canonical diagnostic-filter laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @filterParseDiagnostics_single_nestingExceeded

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic) (diagnostic : ParseDiagnostic)
    (member : diagnostic ∈ filterParseDiagnostics file lexical parsed) :
    diagnostic ∈ parsed :=
  mem_of_mem_filterParseDiagnostics file lexical parsed diagnostic member

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (parsed : List ParseDiagnostic)
    (valid : ∀ diagnostic ∈ parsed, diagnostic.span.ValidFor file) :
    ∀ diagnostic ∈ filterParseDiagnostics file lexical parsed,
      diagnostic.span.ValidFor file :=
  filterParseDiagnostics_spans_validFor file lexical parsed valid

end Tests
