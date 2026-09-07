import Solcore.Syntax.Parser.ProxyExpressionSuccessTraceProperties
import Solcore.Syntax.Parser.ProxyExpressionRejectionTraceProperties
import Solcore.Syntax.Parser.TypeExprTraceUnrestrictedProperties
import Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceProperties
import Solcore.Syntax.DeclarativeTypeExprTraceStructuralProperties

/-! Concrete recursive-type specialization of the raw proxy-expression trace.
All five execution contracts hold on arbitrary states without caller-supplied
type laws. The marker is silent, nested events remain ordered, and a terminal
Failure is not committed. This does not describe the full expression dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

theorem proxyExpression_concrete_trace_success_sound :
    ExpressionTraceSuccessSound proxyExpression (ProxyExpressionTraceParses TypeExprTraceParses) :=
  proxyExpression_trace_success_sound typeExpr_trace_success_sound

theorem proxyExpression_concrete_trace_success_complete :
    ExpressionTraceSuccessComplete proxyExpression (ProxyExpressionTraceParses TypeExprTraceParses) :=
  proxyExpression_trace_success_complete typeExpr_trace_success_complete

theorem proxyExpression_concrete_success_context : ExpressionSuccessContext proxyExpression :=
  proxyExpression_success_context typeExpr_success_context

theorem proxyExpression_concrete_reject_trace_sound :
    ExpressionTraceRejectSound proxyExpression (ProxyExpressionTraceRejects TypeExprTraceRejects) :=
  proxyExpression_reject_trace_sound typeExpr_reject_trace_sound

theorem proxyExpression_concrete_trace_reject_complete :
    ExpressionTraceRejectComplete proxyExpression (ProxyExpressionTraceRejects TypeExprTraceRejects) :=
  proxyExpression_trace_reject_complete typeExpr_trace_reject_complete

theorem proxyExpression_concrete_trace_success_iff
    {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ProxyExpressionTraceParses TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, proxyExpression input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  proxyExpression_trace_success_iff typeExpr_trace_success_sound typeExpr_trace_success_complete

theorem proxyExpression_concrete_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ProxyExpressionTraceRejects TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  proxyExpression_trace_reject_iff typeExpr_reject_trace_sound typeExpr_trace_reject_complete

theorem proxyExpression_concrete_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ProxyExpressionTraceRejects TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  proxyExpression_trace_reject_failure_iff typeExpr_reject_trace_sound typeExpr_trace_reject_complete

/-- Independent exactness of the specialized relations; this bundle expresses
uniqueness and disjointness, not existence of an outcome. -/
theorem proxyExpression_concrete_trace_exactOutcomeSpec {source : SourceId} {endByte : Nat} :
    ExpressionTraceExactOutcomeSpec (ProxyExpressionTraceParses TypeExprTraceParses)
      (ProxyExpressionTraceRejects TypeExprTraceRejects) source endByte :=
  proxyExpressionTraceExactOutcomeSpec typeExprTraceExactOutcomeSpec

theorem proxyExpression_concrete_trace_success_cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Expr} {trace : List ParseDiagnostic}
    (parsed : ProxyExpressionTraceParses TypeExprTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  parsed.cascadeFilters (fun child => child.cascadeFilters text lexical)

/-- Only emitted events are protected, not the separate terminal report. -/
theorem proxyExpression_concrete_trace_reject_cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyExpressionTraceRejects TypeExprTraceRejects source endByte
      input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  rejection.cascadeFilters (fun child => child.cascadeFilters text lexical)

end Solcore.Syntax.Parser.ExpressionAtomInternals
