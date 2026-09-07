import Solcore.Syntax.DeclarativeNamedTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeQualifiedNameRejectionTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceProtectionProperties

/-! Earlier checked names and protected argument-child events remain in full
order on rejection. The final unexpected report is never committed here. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem NamedTypeTraceRejects.cascadeFilters
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | nameRejected name => exact name.cascadeFilters text lexical
  | argumentsRejected name arguments =>
      exact (name.cascadeFilters text lexical).append (arguments.cascadeFilters successProtected rejectProtected)

end Solcore.Syntax.DeclarativeGrammar
