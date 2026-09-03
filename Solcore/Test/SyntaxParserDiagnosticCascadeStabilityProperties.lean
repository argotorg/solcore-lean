import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Repeated and partitioned normalization retains the same complete reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDiagnosticCascadeStabilityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @ParseDiagnosticCascadeFilters.retained_not_suppressed
example := @parseDiagnosticCascadeFilters_of_retained
example := @ParseDiagnosticCascadeFilters.stable
example := @filterParseDiagnostics_idempotent
example := @filterParseDiagnostics_append

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    {raw kept again : List ParseDiagnostic}
    (first : ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) raw kept)
    (second : ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) kept again) :
    again = kept :=
  second.output_unique first.stable

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    (left right : List ParseDiagnostic) :
    filterParseDiagnostics file lexical
      (filterParseDiagnostics file lexical left ++ filterParseDiagnostics file lexical right) =
      filterParseDiagnostics file lexical (left ++ right) := by
  rw [filterParseDiagnostics_append, filterParseDiagnostics_idempotent,
    filterParseDiagnostics_idempotent, filterParseDiagnostics_append]

end Solcore.Test.SyntaxParserDiagnosticCascadeStabilityProperties
