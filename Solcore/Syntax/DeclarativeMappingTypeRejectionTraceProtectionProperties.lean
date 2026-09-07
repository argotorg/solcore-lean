import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeParseDiagnosticCascadeProperties

/-! Mapping rejection protects only the existing key/value event suffix, in
its original order and multiplicity; its separate report remains uncommitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem MappingTypeTraceRejects.cascadeFilters
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {text : String} {lexical : List SourceSpan}
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters text lexical trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    ParseDiagnosticCascadeFilters text lexical trace trace := by
  cases rejection with
  | markerMissing | openingMissing => exact .nil
  | keyRejected _ _ _ _ key => exact rejectProtected key
  | arrowMissing _ _ _ _ key => exact successProtected key
  | valueRejected _ _ _ _ _ key _ value => exact (successProtected key).append (rejectProtected value)
  | closingMissing _ _ _ _ _ key _ value => exact (successProtected key).append (successProtected value)

end Solcore.Syntax.DeclarativeGrammar
