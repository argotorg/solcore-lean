import Solcore.Syntax.DeclarativeTraceOutcomeSpec
import Solcore.Syntax.DeclarativeDotConstructorTraceProperties
import Solcore.Syntax.DeclarativeDotConstructorRejectionTraceProperties

/-! Independent joint exactness for optional arguments and raw leading-dot
constructors. Child laws determine values, endpoints, reports, and whole event
sequences; neither existence nor general recursive expression execution is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable {elementTrace : SourceId → Nat → Remainder → Syntax.Expr →
    Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem optionalDotConstructorArgumentsTraceExactOutcomeSpec
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    TraceExactOutcomeSpec (OptionalDotConstructorArgumentsTraceParses elementTrace)
      (OptionalDotConstructorArgumentsTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := OptionalDotConstructorArgumentsTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := OptionalDotConstructorArgumentsTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := by
    rintro input rejected diagnostic trace rejection ⟨arguments, output, events, success⟩
    exact rejection.disjoint_success elements.successResultUnique elements.successRejectDisjoint success

theorem dotConstructorTraceExactOutcomeSpec
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    ExpressionTraceExactOutcomeSpec (DotConstructorTraceParses elementTrace)
      (DotConstructorTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := DotConstructorTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := DotConstructorTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := by
    rintro input rejected diagnostic trace rejection ⟨value, output, events, success⟩
    exact rejection.disjoint_success elements.successResultUnique elements.successRejectDisjoint success

end Solcore.Syntax.DeclarativeGrammar
