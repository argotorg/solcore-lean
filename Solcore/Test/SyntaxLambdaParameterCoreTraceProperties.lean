import Solcore.Syntax.Parser.LambdaParameterCoreTraceExistenceProperties
import Solcore.Test.SyntaxLambdaParameterRawTraceProperties

/-! Selected-core consumers reconstruct whole replies from independent raw
components. All input states and prior events are arbitrary; neither child
execution contracts nor diagnostic-free premises are needed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaParameterCoreTraceProperties

open Syntax Syntax.Parser Syntax.Parser.LambdaParameterInternals
open Syntax.DeclarativeGrammar

private def stateFrom (source : SourceId) (endByte : Nat) (before : Remainder)
    (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := before.tokens, cursor := before.cursor
  window := { endIndex := before.endIndex, endByte }, diagnosticsRev := prior.reverse
}

private theorem restore_ordinary_priority
    {source : SourceId} {endByte : Nat} {before after rejected : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic} {failure : Failure}
    (prior : List ParseDiagnostic)
    (absent : ComptimeParameterPrefixAbsentAt before)
    (ordinary : OrdinaryLambdaParameterTraceParses source endByte before value after trace)
    (rawRejected : ComptimeLambdaParameterTraceRejects source endByte before rejected failure.toDiagnostic []) :
    lambdaParameterCore (stateFrom source endByte before prior) =
      .ok value ((stateFrom source endByte before prior).traceResult after trace) ∧
    comptimeLambdaParameter (stateFrom source endByte before prior) =
      .reject failure ((stateFrom source endByte before prior).traceResult rejected []) ∧
    ¬ ∃ rejected report events, LambdaParameterCoreTraceRejects source endByte before rejected report events := by
  have selected := LambdaParameterCoreTraceParses.ordinary absent ordinary
  refine ⟨lambdaParameterCore_trace_success_state_iff.mp selected,
    comptimeLambdaParameter_trace_reject_failure_state_iff.mp rawRejected, ?_⟩
  rintro ⟨_, _, _, rejection⟩
  exact rejection.disjoint_success ⟨_, _, _, selected⟩

/-- Reuse the independently constructed `comptime;` fixture. Its ordinary
inferred success wins; the raw comptime identifier failure is not a selected
failure. Existing events, including duplicate constraints, stay first. -/
theorem bare_comptime_selects_success_not_raw_early_failure (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : LambdaParameter) (after : Remainder)
      (trace : List ParseDiagnostic) (failure : Failure) (rejected : Remainder),
      input.diagnostics = prior ∧
      lambdaParameterCore input = .ok value (input.traceResult after trace) ∧
      comptimeLambdaParameter input = .reject failure (input.traceResult rejected []) ∧
      (¬ ∃ after report events, LambdaParameterCoreTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder after report events) ∧
      (∃ name, value.value = .inferred name ∧ name.value = "comptime") ∧
      trace.map (·.kind) = [.constraintViolation .comptimeUsedAsParameterName] ∧
      failure.expected = { head := .identifier, tail := [] } ∧ failure.context = .parameter ∧
      failure.found = some (.symbol .semicolon) ∧
      (input.traceResult after trace).diagnostics = prior ++ trace ∧
      (input.traceResult rejected []).diagnostics = prior ∧
      (input.traceResult after trace).peek?.map (·.value) = some (.symbol .semicolon) := by
  have witnesses := SyntaxLambdaParameterRawTraceProperties.bare_comptime_raw_traces
  have replies := restore_ordinary_priority prior witnesses.2.2 witnesses.1 witnesses.2.1
  refine ⟨_, _, _, _, _, _, ?_, replies.1, replies.2.1, replies.2.2,
    ⟨_, rfl, rfl⟩, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse, List.append_nil]

private theorem restore_ordinary_success
    {source : SourceId} {endByte : Nat} {before after : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic} (prior : List ParseDiagnostic)
    (absent : ComptimeParameterPrefixAbsentAt before)
    (parsed : OrdinaryLambdaParameterTraceParses source endByte before value after trace) :
    lambdaParameterCore (stateFrom source endByte before prior) =
      .ok value ((stateFrom source endByte before prior).traceResult after trace) :=
  lambdaParameterCore_trace_success_state_iff.mp (.ordinary absent parsed)

private theorem comptime_prefix_of_success
    {source : SourceId} {endByte : Nat} {before after : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTraceParses source endByte before value after trace) :
    ComptimeLambdaParameterStartsAt before := by
  cases parsed with
  | parsed markerSpan marker checked _ =>
      rcases marker with ⟨token, rfl⟩
      exact ⟨markerSpan, _, _, token, (identifierTraceParses_iff.mp checked).1.1⟩

private theorem restore_comptime_success
    {source : SourceId} {endByte : Nat} {before after : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic} (prior : List ParseDiagnostic)
    (parsed : ComptimeLambdaParameterTraceParses source endByte before value after trace) :
    lambdaParameterCore (stateFrom source endByte before prior) =
      .ok value ((stateFrom source endByte before prior).traceResult after trace) :=
  lambdaParameterCore_trace_success_state_iff.mp (.comptime (comptime_prefix_of_success parsed) parsed)

/-- Reuse the raw nested-type witness: name checking, child checking, and the
outer-comptime finishing constraint stay in that order after pair selection. -/
theorem selected_nested_type_keeps_all_three_events (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : LambdaParameter) (after : Remainder) (trace : List ParseDiagnostic),
      input.diagnostics = prior ∧ lambdaParameterCore input = .ok value (input.traceResult after trace) ∧
      value.span.startByte = 0 ∧ value.span.endByte = 18 ∧
      (∃ name type, value.value = .typed none name type ∧ name.value = "a-b" ∧ ¬ ParameterTypeAllowed type) ∧
      trace.map (·.kind) = [.invalidIdentifierHyphen "a-b", .invalidIdentifierHyphen "c-d",
        .constraintViolation .comptimeTypeInParameter] ∧
      (input.traceResult after trace).diagnostics = prior ++ trace ∧
      (input.traceResult after trace).peek?.map (·.value) = some (.symbol .semicolon) := by
  have result := restore_ordinary_success prior SyntaxLambdaParameterRawTraceProperties.typed_prefix_absent
    SyntaxLambdaParameterRawTraceProperties.typed_trace
  refine ⟨_, _, _, _, ?_, result, rfl, rfl, ⟨_, _, rfl, rfl, fun allowed => allowed⟩, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]

/-- The selected second `comptime` name is typed without the ordinary-name
warning. A silent raw witness remains silent at the complete selected reply. -/
theorem selected_second_comptime_name_adds_no_warning (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : LambdaParameter) (after : Remainder),
      input.diagnostics = prior ∧ lambdaParameterCore input = .ok value (input.traceResult after []) ∧
      (∃ marker name type, value.value = .typed (some marker) name type ∧ name.value = "comptime") ∧
      value.span.startByte = 0 ∧ value.span.endByte = 20 ∧
      (input.traceResult after []).diagnostics = prior ∧
      (input.traceResult after []).peek?.map (·.value) = some (.symbol .semicolon) := by
  have result := restore_comptime_success prior SyntaxLambdaParameterRawTraceProperties.marked_trace
  refine ⟨_, _, _, ?_, result, ⟨_, _, _, rfl, rfl⟩, rfl, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse, List.append_nil]

/-- Pair selection keeps the marked missing-type error, not ordinary inference
or a name warning. Its event and error node have the same marker/name cover. -/
theorem selected_marked_missing_type_keeps_cover_error (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : LambdaParameter) (after : Remainder) (event : ParseDiagnostic),
      input.diagnostics = prior ∧ lambdaParameterCore input = .ok value (input.traceResult after [event]) ∧
      value.value = .error ∧ value.span.startByte = 0 ∧ value.span.endByte = 17 ∧
      event.span = value.span ∧ event.kind = .constraintViolation .comptimeParameterRequiresType ∧
      (input.traceResult after [event]).diagnostics = prior ++ [event] ∧
      (input.traceResult after [event]).peek?.map (·.value) = some (.symbol .rightParen) := by
  have result := restore_comptime_success prior SyntaxLambdaParameterRawTraceProperties.marked_missing_trace
  refine ⟨_, _, _, _, ?_, result, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]

private theorem restore_ordinary_rejection
    {source : SourceId} {endByte : Nat} {before after : Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} (prior : List ParseDiagnostic)
    (absent : ComptimeParameterPrefixAbsentAt before)
    (rejected : OrdinaryLambdaParameterTraceRejects source endByte before after failure.toDiagnostic trace) :
    lambdaParameterCore (stateFrom source endByte before prior) =
      .reject failure ((stateFrom source endByte before prior).traceResult after trace) :=
  lambdaParameterCore_trace_reject_failure_state_iff.mp (.ordinary absent rejected)

/-- A selected child rejection preserves the name event but does not emit its
terminal report or any finishing event. The complete Failure is retained. -/
theorem selected_child_failure_keeps_only_prior_and_name_event (prior : List ParseDiagnostic) :
    ∃ (input : State) (after : Remainder) (failure : Failure) (trace : List ParseDiagnostic),
      input.diagnostics = prior ∧ lambdaParameterCore input = .reject failure (input.traceResult after trace) ∧
      trace.map (·.kind) = [.invalidIdentifierHyphen "a-b"] ∧
      failure.expected = { head := .typeExpr, tail := [] } ∧ failure.context = .typeExpr ∧
      failure.found = some (.symbol .plus) ∧
      (input.traceResult after trace).diagnostics = prior ++ trace ∧
      (input.traceResult after trace).peek?.map (·.value) = some (.symbol .plus) := by
  have result := restore_ordinary_rejection prior SyntaxLambdaParameterRawTraceProperties.reject_prefix_absent
    SyntaxLambdaParameterRawTraceProperties.rejected_trace
  refine ⟨_, _, _, _, ?_, result, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]

/-- Ordinary execution supplies existence, independently of joint uniqueness.
Every arbitrary State has a protected exact suffix and a reconstructed reply. -/
theorem every_state_has_a_protected_exact_core_reply (input : State) (lexical : List SourceSpan) :
    ∃ trace, ParseDiagnosticCascadeFilters input.file.content lexical trace trace ∧
      ((∃ value after,
        lambdaParameterCore input = .ok value (input.traceResult after trace) ∧
        LambdaParameterCoreTraceParses input.file.id input.window.endByte
          input.declarativeRemainder value after trace) ∨
       (∃ failure after,
        lambdaParameterCore input = .reject failure (input.traceResult after trace) ∧
        LambdaParameterCoreTraceRejects input.file.id input.window.endByte
          input.declarativeRemainder after failure.toDiagnostic trace)) := by
  rcases lambdaParameterCore_exists_trace_outcome input with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact ⟨trace, parsed.cascadeFilters _ _, .inl
      ⟨value, output.declarativeRemainder, lambdaParameterCore_trace_success_state_iff.mp parsed, parsed⟩⟩
  · exact ⟨trace, rejection.cascadeFilters _ _, .inr
      ⟨failure, rejected.declarativeRemainder, lambdaParameterCore_trace_reject_failure_state_iff.mp rejection, rejection⟩⟩

end Solcore.Test.SyntaxLambdaParameterCoreTraceProperties
