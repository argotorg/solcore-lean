import Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceGrammar
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Exact raw proxy rejection uses contracts for the actual type parser.
The marker contributes no event, and nested failures preserve their complete
Failure and returned State without requiring successful context or token laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {typeRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem proxyExpression_reject_iff_components {input rejected : State} {failure : Failure} :
    proxyExpression input = .reject failure rejected ↔
    symbol .at .expression input = .reject failure rejected ∨
      ∃ marker afterMarker, symbol .at .expression input = .ok marker afterMarker ∧
        typeExpr afterMarker = .reject failure rejected := by
  constructor
  · intro result
    unfold proxyExpression at result
    cases markerResult : symbol .at .expression input with
    | invariant => simp only [bind, markerResult] at result; contradiction
    | reject markerFailure markerRejected =>
        simp only [bind, markerResult] at result
        cases result
        exact .inl rfl
    | ok marker afterMarker =>
        simp only [bind, markerResult] at result
        cases typeResult : typeExpr afterMarker with
        | invariant => simp only [typeResult] at result; contradiction
        | ok => simp only [typeResult, pure] at result; contradiction
        | reject typeFailure typeRejected =>
            simp only [typeResult] at result
            cases result
            exact .inr ⟨marker, afterMarker, rfl, typeResult⟩
  · rintro (markerResult | ⟨marker, afterMarker, markerResult, typeResult⟩)
    · simp only [proxyExpression, bind, markerResult]
    · simp only [proxyExpression, bind, markerResult, typeResult]

theorem proxyExpression_reject_trace_sound
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects) :
    ExpressionTraceRejectSound proxyExpression (DeclarativeGrammar.ProxyExpressionTraceRejects typeRejects) := by
  intro input rejected failure result
  rcases proxyExpression_reject_iff_components.mp result with markerResult |
      ⟨marker, afterMarker, markerResult, typeResult⟩
  · have same := symbol_reject_state_eq .at .expression markerResult
    subst rejected
    have reported := (symbol_reject_reports_iff .at .expression).mpr ⟨failure, markerResult, rfl⟩
    exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  · have markerParsed := symbol_success_exactTokenParses .at .expression markerResult
    have markerState := (symbol_ok_tokenAt .at .expression markerResult).2
    subst afterMarker
    rcases rejectSound typeResult with ⟨trace, typed, events⟩
    exact ⟨trace, .typeRejected marker.span markerParsed typed, events⟩

theorem proxyExpression_trace_reject_complete
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects) :
    ExpressionTraceRejectComplete proxyExpression (DeclarativeGrammar.ProxyExpressionTraceRejects typeRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (symbol_reject_reports_iff .at .expression).mp ⟨absent, reported⟩ with
        ⟨failure, markerResult, reportEq⟩
      exact ⟨failure, input, proxyExpression_reject_iff_components.mpr (.inl markerResult),
        rfl, reportEq, by simp⟩
  | typeRejected markerSpan marker typed =>
      have markerResult := symbol_eq_ok_of_exactTokenParses .at .expression marker
      rcases marker with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) typed with
        ⟨failure, rejected, typeResult, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, proxyExpression_reject_iff_components.mpr
        (.inr ⟨_, _, markerResult, typeResult⟩), afterEq, reportEq, events⟩

theorem proxyExpression_trace_reject_iff
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects)
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyExpressionTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact proxyExpression_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases proxyExpression_reject_trace_sound rejectSound result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem proxyExpression_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound typeExpr typeRejects)
    (rejectComplete : ParserTraceRejectComplete typeExpr typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyExpressionTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [proxyExpression_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
