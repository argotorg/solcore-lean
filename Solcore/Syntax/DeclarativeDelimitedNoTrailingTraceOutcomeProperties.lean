import Solcore.Syntax.DeclarativeTraceOutcomeSpec
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingRejectionTraceProperties

/-! Joint exactness for no-trailing list traces under independent child laws.
The result fixes ASTs, remainders, reports, and complete event lists. It neither
asserts that an outcome exists nor identifies a concrete child implementation. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem noTrailingDelimitedListTraceExactOutcomeSpec {α : Type}
    {elementTrace : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext)
    (elements : TraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec
      (NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace)
      (NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace elementRejects)
      source endByte where
  successResultUnique := NoTrailingDelimitedListTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := NoTrailingDelimitedListTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := NoTrailingDelimitedListTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
