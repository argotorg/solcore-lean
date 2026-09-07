import Solcore.Syntax.DeclarativeTraceOutcomeSpec
import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceProperties

/-! Independent optional-argument exactness fixes complete outcomes without
asserting their existence or assuming recursive type execution. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem namedTypeArgumentsTraceExactOutcomeSpec
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (NamedTypeArgumentsTraceParses elementTrace)
      (NamedTypeArgumentsTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := NamedTypeArgumentsTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := NamedTypeArgumentsTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := NamedTypeArgumentsTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
