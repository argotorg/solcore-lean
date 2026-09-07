import Solcore.Syntax.Parser.TypeExprTraceCompletenessProperties
import Solcore.Syntax.Parser.TypeUnrestrictedFuelTotalityProperties

/-! Complete recursive type trace correspondence on arbitrary states. Production
totality discharges invariant exclusion without validity, canonical lexing,
prior-diagnostic, or child-contract assumptions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem typeExpr_trace_success_complete : ParserTraceSuccessComplete typeExpr TypeExprTraceParses :=
  trace_success_complete_of_sound typeExpr_trace_success_sound typeExpr_reject_trace_sound
    (fun _ _ => typeExprTraceExactOutcomeSpec) typeExpr_ne_invariant_unrestricted

theorem typeExpr_trace_reject_complete : ParserTraceRejectComplete typeExpr TypeExprTraceRejects :=
  trace_reject_complete_of_sound typeExpr_trace_success_sound typeExpr_reject_trace_sound
    (fun _ _ => typeExprTraceExactOutcomeSpec) typeExpr_ne_invariant_unrestricted

theorem typeExpr_trace_success_iff
    {input : State} {value : TypeExpr} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_success_iff_of_ne_invariant (typeExpr_ne_invariant_unrestricted input)

theorem typeExpr_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_iff_of_ne_invariant (typeExpr_ne_invariant_unrestricted input)

theorem typeExpr_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_failure_iff_of_ne_invariant (typeExpr_ne_invariant_unrestricted input)

end Solcore.Syntax.Parser
