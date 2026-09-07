import Solcore.Syntax.Parser.OptionalLambdaReturnTypeRejectionTraceProperties
import Solcore.Syntax.Parser.TypeExprTraceUnrestrictedProperties
import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceExactnessProperties
import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceProtectionProperties
import Solcore.Syntax.DeclarativeTypeExprTraceStructuralProperties

/-! Concrete recursive-type specialization of an optional lambda return type.
The absent arrow returns none without changing state; a present arrow carries
exactly the recursive type events or complete Failure. No caller-supplied child
law or state validity is required. These are not full-lambda parser contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

theorem optionalLambdaReturnType_concrete_trace_success_sound :
    ParserTraceSuccessSound optionalLambdaReturnType
      (OptionalLambdaReturnTypeTraceParses TypeExprTraceParses) :=
  optionalLambdaReturnType_trace_success_sound typeExpr_trace_success_sound

theorem optionalLambdaReturnType_concrete_trace_success_complete :
    ParserTraceSuccessComplete optionalLambdaReturnType
      (OptionalLambdaReturnTypeTraceParses TypeExprTraceParses) :=
  optionalLambdaReturnType_trace_success_complete typeExpr_trace_success_complete

theorem optionalLambdaReturnType_concrete_success_context :
    ParserSuccessContext optionalLambdaReturnType :=
  optionalLambdaReturnType_success_context typeExpr_success_context

theorem optionalLambdaReturnType_concrete_reject_trace_sound :
    ParserTraceRejectSound optionalLambdaReturnType
      (OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects) :=
  optionalLambdaReturnType_reject_trace_sound typeExpr_reject_trace_sound

theorem optionalLambdaReturnType_concrete_trace_reject_complete :
    ParserTraceRejectComplete optionalLambdaReturnType
      (OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects) :=
  optionalLambdaReturnType_trace_reject_complete typeExpr_trace_reject_complete

theorem optionalLambdaReturnType_concrete_trace_success_iff
    {input : State} {value : Option TypeExpr} {after : Remainder} {trace : List ParseDiagnostic} :
    OptionalLambdaReturnTypeTraceParses TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, optionalLambdaReturnType input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  optionalLambdaReturnType_trace_success_iff typeExpr_trace_success_sound typeExpr_trace_success_complete

theorem optionalLambdaReturnType_concrete_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  optionalLambdaReturnType_trace_reject_iff typeExpr_reject_trace_sound typeExpr_trace_reject_complete

theorem optionalLambdaReturnType_concrete_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  optionalLambdaReturnType_trace_reject_failure_iff typeExpr_reject_trace_sound typeExpr_trace_reject_complete

/-- Independent uniqueness and disjointness after fixing the child relations;
the bundle itself is not an outcome-existence claim. -/
theorem optionalLambdaReturnType_concrete_trace_exactOutcomeSpec {source : SourceId} {endByte : Nat} :
    TraceExactOutcomeSpec (OptionalLambdaReturnTypeTraceParses TypeExprTraceParses)
      (OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects) source endByte :=
  optionalLambdaReturnTypeTraceExactOutcomeSpec typeExprTraceExactOutcomeSpec

theorem optionalLambdaReturnType_concrete_trace_success_cascadeFilters
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : Option TypeExpr} {trace : List ParseDiagnostic}
    (parsed : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  parsed.cascadeFilters (fun child => child.cascadeFilters text lexical)

/-- Only emitted events are protected, not the separate terminal report. -/
theorem optionalLambdaReturnType_concrete_trace_reject_cascadeFilters
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects source endByte
      input rejected report trace)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  rejection.cascadeFilters (fun child => child.cascadeFilters text lexical)

end Solcore.Syntax.Parser.ExpressionAtomInternals
