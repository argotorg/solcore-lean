import Solcore.Syntax.DeclarativeTraceOutcomeSpec
import Solcore.Syntax.DeclarativeMappingTypeTraceProperties
import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceProperties

/-! Raw mapping outcomes are unique and disjoint under independent child laws.
This bundle asserts neither existence nor prioritized dispatcher selection. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem mappingTypeTraceExactOutcomeSpec
    {elementTrace : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (MappingTypeTraceParses elementTrace)
      (MappingTypeTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := MappingTypeTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := MappingTypeTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := MappingTypeTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
