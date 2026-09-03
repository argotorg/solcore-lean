import Solcore.Syntax.DeclarativeIdentifierTraceProperties
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Identifier spelling traces have no removable lexical-cascade events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every identifier event is protected, including repeated hyphens in its text. -/
theorem IdentifierDiagnosticTrace.not_candidate
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (diagnostics : IdentifierDiagnosticTrace name trace) :
    ∀ diagnostic ∈ trace, ¬ LexicalCascadeCandidate diagnostic.kind := by
  cases diagnostics with
  | clean absent => simp
  | hyphen present =>
      intro diagnostic member
      have exactDiagnostic : diagnostic =
          { span := name.span, kind := .invalidIdentifierHyphen name.value } := by
        simpa only [List.mem_singleton] using member
      subst diagnostic
      exact id

/-- Lexical errors never suppress an independent identifier spelling trace. -/
theorem IdentifierDiagnosticTrace.cascadeFilters
    {name : Syntax.Identifier} {trace : List ParseDiagnostic}
    (diagnostics : IdentifierDiagnosticTrace name trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace trace :=
  parseDiagnosticCascadeFilters_of_protected source lexical diagnostics.not_candidate

end Solcore.Syntax.DeclarativeGrammar
