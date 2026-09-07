import Solcore.Syntax.Parser.TypeExprTraceUnrestrictedProperties
import Solcore.Syntax.Parser.TypeSourceFrameProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! Recursive trace correspondence fixes the whole successful/rejected state,
not just a cursor and event suffix. The rebuilt state carries every independent
remainder field, so no token or end-index mismatch is silently forgotten. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem typeExpr_trace_success_state_iff
    {input : State} {value : TypeExpr} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      typeExpr input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases typeExpr_trace_success_iff.mp parsed with ⟨output, result, afterEq, events⟩
    have frame := typeExpr_success_context result
    have stateEq := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact stateEq ▸ result
  · intro result
    exact typeExpr_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem typeExpr_trace_reject_failure_state_iff
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      typeExpr input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases typeExpr_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have window := typeExpr_preservesTokenWindow input
    rw [result] at window
    have stateEq := State.eq_traceResult_of_fields (typeExpr_preservesFile.file_eq_of_reject result)
      (congrArg TokenWindow.endByte window.2) afterEq events
    exact stateEq ▸ result
  · intro result
    exact typeExpr_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem typeExpr_trace_reject_state_iff
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, typeExpr input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases typeExpr_trace_reject_iff.mp rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, typeExpr_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ typeExpr_trace_reject_failure_state_iff.mpr result

end Solcore.Syntax.Parser
