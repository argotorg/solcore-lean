import Solcore.Syntax.DeclarativeExpressionTraceOutcomeSpec
import Solcore.Syntax.DeclarativeParenthesizedTraceExactnessProperties
import Solcore.Syntax.DeclarativeParenthesizedTraceDisjointnessProperties

/-! Independent exact parenthesized outcomes lift child uniqueness and
disjointness. This includes raw opening rejection without asserting existence,
concrete recursive execution, or a parser-state equality beyond the traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem parenthesizedTraceExactOutcomeSpec
    {elementTrace : SourceId → Nat → Remainder → Syntax.Expr → Remainder → List ParseDiagnostic → Prop}
    {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (elements : ExpressionTraceExactOutcomeSpec elementTrace elementRejects source endByte) :
    ExpressionTraceExactOutcomeSpec (ParenthesizedExpressionTraceParses elementTrace)
      (ParenthesizedExpressionTraceRejects elementTrace elementRejects) source endByte where
  successResultUnique := ParenthesizedExpressionTraceParses.result_unique elements.successResultUnique
  rejectResultUnique := ParenthesizedExpressionTraceRejects.result_unique elements.successResultUnique
    elements.rejectResultUnique elements.successRejectDisjoint
  successRejectDisjoint := ParenthesizedExpressionTraceRejects.disjoint_success elements.successResultUnique
    elements.successRejectDisjoint

end Solcore.Syntax.DeclarativeGrammar
