import Solcore.Syntax.DeclarativeIdentifierCascadeProperties
import Solcore.Syntax.DeclarativePragmaTraceGrammar

/-! The ordered checked-item events of successful pragmas are all protected
from lexical-cascade suppression, including repeated spelling diagnostics. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Concatenating protected identifier events preserves the full ordered trace. -/
theorem IdentifierListDiagnosticTrace.cascadeFilters
    {names : List Syntax.Identifier} {trace : List ParseDiagnostic}
    (diagnostics : IdentifierListDiagnosticTrace names trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace trace := by
  induction diagnostics with
  | nil => exact .nil
  | cons head tail ih => exact (head.cascadeFilters source lexical).append ih

/-- Successful pragma traces contain no removable expectation or recovery event. -/
theorem PragmaDeclTraceParses.cascadeFilters
    {input output : Remainder} {declaration : Syntax.PragmaDecl}
    {trace : List ParseDiagnostic}
    (parsed : PragmaDeclTraceParses input declaration output trace)
    (source : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters source lexical trace trace :=
  parsed.2.cascadeFilters source lexical

end Solcore.Syntax.DeclarativeGrammar
