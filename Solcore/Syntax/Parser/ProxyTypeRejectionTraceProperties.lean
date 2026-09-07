import Solcore.Syntax.DeclarativeProxyTypeRejectionTraceGrammar
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Type

/-! Exact raw proxy-type rejection uses only nested rejection contracts.
The marker contributes no event, and nested failures preserve their complete
Failure and returned State without requiring successful context or token laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {typeRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parseProxyType_reject_iff_components {input rejected : State} {failure : Failure} :
    parseProxyType nested input = .reject failure rejected ↔
    symbol .at .typeExpr input = .reject failure rejected ∨
      ∃ marker afterMarker, symbol .at .typeExpr input = .ok marker afterMarker ∧
        nested afterMarker = .reject failure rejected := by
  constructor
  · intro result
    unfold parseProxyType at result
    cases markerResult : symbol .at .typeExpr input with
    | invariant => simp only [markerResult] at result; contradiction
    | reject markerFailure markerRejected =>
        simp only [markerResult] at result
        cases result
        exact .inl rfl
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases typeResult : nested afterMarker with
        | invariant => simp only [typeResult] at result; contradiction
        | ok => simp only [typeResult] at result; contradiction
        | reject typeFailure innerRejected =>
            simp only [typeResult] at result
            cases result
            exact .inr ⟨marker, afterMarker, rfl, typeResult⟩
  · rintro (markerResult | ⟨marker, afterMarker, markerResult, typeResult⟩)
    · simp only [parseProxyType, markerResult]
    · simp only [parseProxyType, markerResult, typeResult]

theorem parseProxyType_reject_trace_sound
    (rejectSound : ParserTraceRejectSound nested typeRejects) :
    ParserTraceRejectSound (parseProxyType nested) (DeclarativeGrammar.ProxyTypeTraceRejects typeRejects) := by
  intro input rejected failure result
  rcases parseProxyType_reject_iff_components.mp result with markerResult |
      ⟨marker, afterMarker, markerResult, typeResult⟩
  · have same := symbol_reject_state_eq .at .typeExpr markerResult
    subst rejected
    have reported := (symbol_reject_reports_iff .at .typeExpr).mpr ⟨failure, markerResult, rfl⟩
    exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  · have markerParsed := symbol_success_exactTokenParses .at .typeExpr markerResult
    have markerState := (symbol_ok_tokenAt .at .typeExpr markerResult).2
    subst afterMarker
    rcases rejectSound typeResult with ⟨trace, typed, events⟩
    exact ⟨trace, .innerRejected marker.span markerParsed typed, events⟩

theorem parseProxyType_trace_reject_complete
    (rejectComplete : ParserTraceRejectComplete nested typeRejects) :
    ParserTraceRejectComplete (parseProxyType nested) (DeclarativeGrammar.ProxyTypeTraceRejects typeRejects) := by
  intro input after report trace rejection
  cases rejection with
  | markerMissing absent reported =>
      rcases (symbol_reject_reports_iff .at .typeExpr).mp ⟨absent, reported⟩ with
        ⟨failure, markerResult, reportEq⟩
      exact ⟨failure, input, parseProxyType_reject_iff_components.mpr (.inl markerResult),
        rfl, reportEq, by simp⟩
  | innerRejected markerSpan marker typed =>
      have markerResult := symbol_eq_ok_of_exactTokenParses .at .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) typed with
        ⟨failure, rejected, typeResult, afterEq, reportEq, events⟩
      exact ⟨failure, rejected, parseProxyType_reject_iff_components.mpr
        (.inr ⟨_, _, markerResult, typeResult⟩), afterEq, reportEq, events⟩

theorem parseProxyType_trace_reject_iff
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyTypeTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parseProxyType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseProxyType_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parseProxyType_reject_trace_sound rejectSound result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parseProxyType_trace_reject_failure_iff
    (rejectSound : ParserTraceRejectSound nested typeRejects)
    (rejectComplete : ParserTraceRejectComplete nested typeRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ProxyTypeTraceRejects typeRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parseProxyType nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parseProxyType_trace_reject_iff rejectSound rejectComplete]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
