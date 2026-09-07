import Solcore.Syntax.DeclarativeTraceOutcomeSpec
import Solcore.Syntax.DeclarativeNamedTypeTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeRejectionTraceProperties

/-! Raw named-type joint exactness under independent recursive child laws.
Neither existence nor the prioritized type dispatch is asserted here. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem namedTypeTraceExactOutcomeSpec
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (NamedTypeTraceParses elementTrace)
      (NamedTypeTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := NamedTypeTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := NamedTypeTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := NamedTypeTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
