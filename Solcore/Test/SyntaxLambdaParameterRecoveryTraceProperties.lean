import Solcore.Syntax.Parser.LambdaParameterRecoveryTraceProperties
import Solcore.Test.SyntaxParameterRecoveryTraceProperties

/-! Standalone lambda recovery changes only the error AST carrier. Independent
traces restore both complete replies; existing function-recovery fixtures are
reused to test delimiter consumption, missing backing, and committed reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaParameterRecoveryTraceProperties

open Syntax Syntax.Parser Syntax.DeclarativeGrammar
open FunctionParameterInternals LambdaParameterInternals

private theorem retag_success {input output : State} {value : FunctionParameter}
    (result : recoverParameter input = .ok value output) :
    recoverLambdaParameter input = .ok { span := value.span, value := .error } output := by
  simp only [recoverLambdaParameter, result]

private theorem retag_rejection {input rejected : State} {failure : Failure}
    (result : recoverParameter input = .reject failure rejected) :
    recoverLambdaParameter input = .reject failure rejected := by
  simp only [recoverLambdaParameter, result]

/-- One independent witness restores both complete replies with exactly the
same source, carrier, window, cursor, and ordered diagnostic suffix. -/
theorem independent_trace_restores_both_replies
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : FunctionParameterRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    LambdaParameterRecoveryTraceParses input.file.id input.window.endByte input.declarativeRemainder
      { span := value.span, value := .error } after trace ∧
    recoverParameter input = .ok value (input.traceResult after trace) ∧
    recoverLambdaParameter input = .ok { span := value.span, value := .error } (input.traceResult after trace) ∧
    (input.traceResult after trace).diagnostics = input.diagnostics ++ [parameterRecoveryTraceEvent value.span] := by
  refine ⟨.recovered parsed, recoverParameter_trace_success_state_iff.mp parsed,
    recoverLambdaParameter_trace_success_state_iff.mp (.recovered parsed), ?_⟩
  rw [State.traceResult_diagnostics, parsed.2]

/-- A terminal recovery Failure is forwarded intact and is not committed by
either wrapper. This does not remove an equal report already present in input. -/
theorem independent_rejection_restores_both_replies
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejected : FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    recoverParameter input = .reject failure (input.traceResult after trace) ∧
    recoverLambdaParameter input = .reject failure (input.traceResult after trace) ∧
    (input.traceResult after trace).diagnostics = input.diagnostics := by
  refine ⟨recoverParameter_trace_reject_failure_state_iff.mp rejected,
    recoverLambdaParameter_trace_reject_failure_state_iff.mp rejected, ?_⟩
  rw [State.traceResult_diagnostics, rejected.2.2, List.append_nil]

/-- Reuse the existing comma / skipped hyphen name / right-parenthesis scan:
the mandatory comma is consumed, while the later right parenthesis is not. -/
theorem mandatory_comma_is_consumed (prior : List ParseDiagnostic) :
    ∃ (input output : State) (value : FunctionParameter),
      recoverParameter input = .ok value output ∧
      recoverLambdaParameter input = .ok { span := value.span, value := .error } output ∧
      input.cursor = 0 ∧ input.peek?.map (·.value) = some (.symbol .comma) ∧
      output.cursor = 2 ∧ output.peek?.map (·.value) = some (.symbol .rightParen) ∧
      value.span.startByte = 0 ∧ value.span.endByte = 4 ∧
      output.diagnostics = prior ++ [parameterRecoveryTraceEvent value.span] := by
  have result := SyntaxParameterRecoveryTraceProperties.mandatory_comma_then_rightParen_stop prior
  exact ⟨_, _, _, result.1, retag_success result.1, rfl, rfl, rfl, rfl, rfl, rfl, result.2.1⟩

/-- Initial right parenthesis has the same mandatory-consumption behavior;
the following comma remains at the identical output State in both parsers. -/
theorem mandatory_rightParen_is_consumed (prior : List ParseDiagnostic) :
    ∃ (input output : State) (value : FunctionParameter),
      recoverParameter input = .ok value output ∧
      recoverLambdaParameter input = .ok { span := value.span, value := .error } output ∧
      input.cursor = 0 ∧ input.peek?.map (·.value) = some (.symbol .rightParen) ∧
      output.cursor = 1 ∧ output.peek?.map (·.value) = some (.symbol .comma) ∧
      value.span.startByte = 0 ∧ value.span.endByte = 1 ∧
      output.diagnostics = prior ++ [parameterRecoveryTraceEvent value.span] := by
  have result := SyntaxParameterRecoveryTraceProperties.mandatory_rightParen_then_comma_stop prior
  refine ⟨_, _, _, result.1, retag_success result.1, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change (parameterRecoveryTraceEvent _ :: prior.reverse).reverse = _
  simp only [List.reverse_cons, List.reverse_reverse]
  rfl

/-- With numeric endIndex 3 but one backing token, an established scan stops
at cursor 1; a fresh recovery there rejects and leaves all prior events intact. -/
theorem missing_backing_scan_stop_and_initial_rejection (prior : List ParseDiagnostic) :
    ∃ (input output missing : State) (value : FunctionParameter) (failure : Failure),
      recoverParameter input = .ok value output ∧
      recoverLambdaParameter input = .ok { span := value.span, value := .error } output ∧
      recoverParameter missing = .reject failure missing ∧
      recoverLambdaParameter missing = .reject failure missing ∧
      input.cursor = 0 ∧ output.cursor = 1 ∧ missing.cursor = 1 ∧
      missing.window.endIndex = 3 ∧ missing.peek? = none ∧ missing.diagnostics = prior ∧
      failure.expected = { head := .identifier, tail := [] } ∧ failure.context = .parameter ∧
      failure.found = none := by
  have result := SyntaxParameterRecoveryTraceProperties.missing_backing_stop_versus_initial_rejection prior
  exact ⟨_, _, _, _, _, result.1, retag_success result.1, result.2.1, retag_rejection result.2.1,
    rfl, rfl, rfl, rfl, result.2.2.2.1, result.2.2.2.2, rfl, rfl, rfl⟩

/-- A token hidden by endIndex zero is not the mandatory first token, even
though the backing array contains it. Both complete rejected States are input. -/
theorem hidden_first_token_is_not_consumed (prior : List ParseDiagnostic) :
    ∃ (input : State) (token : Token) (failure : Failure),
      input.cursor = 0 ∧ input.window.endIndex = 0 ∧ input.tokens[0]? = some token ∧
      token.value = .symbol .plus ∧
      recoverParameter input = .reject failure input ∧
      recoverLambdaParameter input = .reject failure input := by
  have result := SyntaxParameterRecoveryTraceProperties.hidden_first_token_rejects_unchanged prior
  exact ⟨_, _, _, rfl, rfl, result.1, rfl, result.2, retag_rejection result.2⟩

/-- The previously committed complete report remains once before recovery's
event. Arbitrary prior duplicates are not deduplicated by the lambda retag. -/
theorem committed_report_is_not_reemitted (prior : List ParseDiagnostic) (original : Failure) :
    ∃ (input output : State) (value : FunctionParameter),
      input.diagnostics = prior ++ [original.toDiagnostic] ∧
      recoverParameter input = .ok value output ∧
      recoverLambdaParameter input = .ok { span := value.span, value := .error } output ∧
      output.diagnostics = prior ++ [original.toDiagnostic, parameterRecoveryTraceEvent value.span] := by
  have result := SyntaxParameterRecoveryTraceProperties.committed_failure_is_not_reemitted prior original
  refine ⟨_, _, _, ?_, result.1, retag_success result.1, result.2⟩
  change (prior ++ [original.toDiagnostic]).reverse.reverse = _
  exact List.reverse_reverse _

/-- Error retagging does not turn the recovery event into a protected event:
the same independently specified trace may be retained or dropped conditionally. -/
theorem recovery_trace_has_conditional_filtering
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    (¬ LexicalCascadeSuppresses text lexical value.span → ParseDiagnosticCascadeFilters text lexical trace trace) ∧
    (LexicalCascadeSuppresses text lexical value.span → ParseDiagnosticCascadeFilters text lexical trace []) :=
  ⟨parsed.cascade_kept text lexical, parsed.cascade_dropped text lexical⟩

/-- The concrete 0..4 scan supplies a lambda trace whose recovered event is
kept without lexical errors but removed by a lexical error on the same span. -/
theorem concrete_recovery_event_is_conditionally_filtered (text : String) :
    ∃ (source : SourceId) (input output : Remainder) (value : LambdaParameter),
      LambdaParameterRecoveryTraceParses source 99 input value output [parameterRecoveryTraceEvent value.span] ∧
      value.value = .error ∧ value.span.startByte = 0 ∧ value.span.endByte = 4 ∧
      filterParseDiagnostics { id := source, content := text } []
        [parameterRecoveryTraceEvent value.span] = [parameterRecoveryTraceEvent value.span] ∧
      filterParseDiagnostics { id := source, content := text }
        [{ span := value.span, kind := .invalidToken }] [parameterRecoveryTraceEvent value.span] = [] := by
  have tested := SyntaxParameterRecoveryTraceProperties.mandatory_comma_then_rightParen_stop []
  rcases recoverParameter_trace_success_sound tested.1 with ⟨trace, parsed, _⟩
  have traceEq := parsed.2
  rw [traceEq] at parsed
  have filtered := SyntaxParameterRecoveryTraceProperties.recovery_event_is_conditionally_filtered text
  exact ⟨_, _, _, _, .recovered parsed, rfl, rfl, rfl, filtered.1, filtered.2⟩

end Solcore.Test.SyntaxLambdaParameterRecoveryTraceProperties
