import Solcore.Syntax.Parser.TypeExprTraceCompletenessProperties

/-! Independent recursive uniqueness fixes every diagnostic event of an actual
execution and excludes an opposite declarative outcome. Valid-state reverse
correspondence is explicitly narrower than unrestricted soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeExprTraceOutcomeProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem actual_success_fixes_every_claimed_trace
    {input output : State} {actual claimed : TypeExpr} {after : Remainder}
    {trace : List ParseDiagnostic} (result : typeExpr input = .ok actual output)
    (parsed : TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder claimed after trace) :
    actual = claimed ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace ∧
      ¬ ∃ rejected report events, TypeExprTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected report events := by
  rcases typeExpr_trace_success_sound result with ⟨actualTrace, actualParsed, events⟩
  rcases actualParsed.result_unique parsed with ⟨valueEq, afterEq, rfl⟩
  exact ⟨valueEq, afterEq, events, parsed.disjoint_rejection⟩

theorem actual_rejection_fixes_report_and_every_claimed_event
    {input rejected : State} {failure : Failure} {after : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : typeExpr input = .reject failure rejected)
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace) :
    rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace ∧
      ¬ ∃ value output events, TypeExprTraceParses input.file.id input.window.endByte
        input.declarativeRemainder value output events := by
  rcases typeExpr_reject_trace_sound result with ⟨actualTrace, actualRejected, events⟩
  rcases actualRejected.result_unique rejection with ⟨afterEq, reportEq, rfl⟩
  exact ⟨afterEq, reportEq, events, rejection.disjoint_success⟩

theorem valid_input_realizes_success_with_exact_events
    {input : State} (inputValid : input.ValidFor) {value : TypeExpr} {after : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace ∧
      ¬ ∃ rejected report events, TypeExprTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected report events := by
  rcases (typeExpr_trace_success_iff_onValid inputValid).mp parsed with
    ⟨output, result, afterEq, events⟩
  exact ⟨output, result, afterEq, events, parsed.disjoint_rejection⟩

theorem valid_input_realizes_complete_failure_without_committing_it
    {input : State} (inputValid : input.ValidFor) {failure : Failure} {after : Remainder}
    {trace : List ParseDiagnostic}
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    ∃ rejected, typeExpr input = .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      rejected.diagnostics = input.diagnostics ++ trace ∧
      ¬ ∃ value output events, TypeExprTraceParses input.file.id input.window.endByte
        input.declarativeRemainder value output events := by
  rcases (typeExpr_trace_reject_failure_iff_onValid inputValid).mp rejection with
    ⟨rejected, result, afterEq, events⟩
  exact ⟨rejected, result, afterEq, events, rejection.disjoint_success⟩

end Solcore.Test.SyntaxTypeExprTraceOutcomeProperties
