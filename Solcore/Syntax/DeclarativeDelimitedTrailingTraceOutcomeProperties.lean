import Solcore.Syntax.DeclarativeTraceOutcomeSpec
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProperties

/-! Joint exactness for trailing-enabled list traces under independent child
laws. It fixes complete outcomes without asserting existence or child execution. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem trailingDelimitedListTraceExactOutcomeSpec {α : Type}
    {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext)
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec
      (TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace)
      (TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects)
      source endByte where
  successResultUnique := TrailingDelimitedListTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := TrailingDelimitedListTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := TrailingDelimitedListTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
