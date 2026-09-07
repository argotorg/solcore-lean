import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceGrammar
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProtectionProperties

/-! Optional argument rejection protects precisely the preceding child-event
suffix. Its final unexpected-token report remains separate and uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem NamedTypeArgumentsTraceRejects.cascadeFilters
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | present _ _ arguments => exact arguments.cascadeFilters successProtected rejectProtected

end Solcore.Syntax.DeclarativeGrammar
