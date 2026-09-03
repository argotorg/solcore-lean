import Solcore.Syntax.DeclarativeParseDiagnosticCascadeStabilityProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties

/-! Executable normalization algebra derived from independent trace rules. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The same lexical context never changes an already normalized trace. -/
theorem filterParseDiagnostics_idempotent (file : SourceFile)
    (lexical : List LexicalDiagnostic) (parsed : List ParseDiagnostic) :
    filterParseDiagnostics file lexical (filterParseDiagnostics file lexical parsed) =
      filterParseDiagnostics file lexical parsed := by
  have filtered := (filterParseDiagnostics_eq_iff_cascadeFilters
    file lexical parsed (filterParseDiagnostics file lexical parsed)).mp rfl
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical filtered.stable

/-- Normalizing concatenated traces preserves their original partition and order. -/
theorem filterParseDiagnostics_append (file : SourceFile)
    (lexical : List LexicalDiagnostic) (left right : List ParseDiagnostic) :
    filterParseDiagnostics file lexical (left ++ right) =
      filterParseDiagnostics file lexical left ++ filterParseDiagnostics file lexical right := by
  have leftFiltered := (filterParseDiagnostics_eq_iff_cascadeFilters
    file lexical left (filterParseDiagnostics file lexical left)).mp rfl
  have rightFiltered := (filterParseDiagnostics_eq_iff_cascadeFilters
    file lexical right (filterParseDiagnostics file lexical right)).mp rfl
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (leftFiltered.append rightFiltered)

end Solcore.Syntax.Parser
