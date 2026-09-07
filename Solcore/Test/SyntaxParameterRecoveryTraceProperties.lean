import Solcore.Syntax.Parser.ParameterRecoveryTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties

/-! Standalone recovery consumes its mandatory first token before testing a
boundary. Independent scans drive complete replies, including malformed token
windows; recovery events have conditional, not protected, cascade behavior. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParameterRecoveryTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open FunctionParameterInternals

private def source : SourceId := { origin := .main, path := "parameter-recovery-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def symbol (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def skipped : Token := { span := span 1 4, value := .identifier "a-b" }
private def scanTokens : List Token := [symbol 0 1 .comma, skipped, symbol 4 5 .rightParen, symbol 5 6 .plus]
private def commaTokens : List Token := [symbol 0 1 .rightParen, symbol 1 2 .comma, symbol 2 3 .plus]
private def sparseTokens : List Token := [symbol 0 1 .plus]
private def remainder (tokens : List Token) (endIndex cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex, cursor
}
private def input (tokens : List Token) (endIndex cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def recovered (startByte endByte : Nat) : FunctionParameter := {
  span := span startByte endByte, value := .error
}
private def event (startByte endByte : Nat) : ParseDiagnostic := parameterRecoveryTraceEvent (span startByte endByte)
private def final (tokens : List Token) (endIndex cursor : Nat) (diagnostic : ParseDiagnostic)
    (prior : List ParseDiagnostic) : State := {
  input tokens endIndex cursor prior with diagnosticsRev := diagnostic :: prior.reverse
}
private def missingFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .identifier, tail := [] }, context := .parameter
}

private theorem scan_trace : FunctionParameterRecoveryTraceParses source 99
    (remainder scanTokens 4 0) (recovered 0 4) (remainder scanTokens 4 2) [event 0 4] := by
  have continues : ¬ FunctionParameterRecoveryStops (remainder scanTokens 4 1) := by
    intro stops
    cases stops with
    | windowEnd atEnd => change 4 ≤ 1 at atEnd; omega
    | comma token => simp [TokenAt, remainder, scanTokens, skipped] at token
    | rightParen token => simp [TokenAt, remainder, scanTokens, skipped] at token
    | missingToken inside missing => simp [remainder, scanTokens] at missing
  refine ⟨.recovered (token := symbol 0 1 .comma) ⟨by change 0 < 4; decide, rfl⟩ ?_, rfl⟩
  exact .next continues (token := skipped) ⟨by change 1 < 4; decide, rfl⟩
    (.stop (.rightParen ⟨by change 2 < 4; decide, rfl⟩))

private theorem comma_trace : FunctionParameterRecoveryTraceParses source 99
    (remainder commaTokens 3 0) (recovered 0 1) (remainder commaTokens 3 1) [event 0 1] :=
  ⟨.recovered (token := symbol 0 1 .rightParen) ⟨by change 0 < 3; decide, rfl⟩
    (.stop (.comma ⟨by change 1 < 3; decide, rfl⟩)), rfl⟩

/-- Initial comma is consumed, the intervening hyphen identifier is skipped
without checking it, and the later right parenthesis is left unread. -/
theorem mandatory_comma_then_rightParen_stop (prior : List ParseDiagnostic) :
    recoverParameter (input scanTokens 4 0 prior) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) prior) ∧
    (final scanTokens 4 2 (event 0 4) prior).diagnostics = prior ++ [event 0 4] ∧
    (final scanTokens 4 2 (event 0 4) prior).peek? = some (symbol 4 5 .rightParen) := by
  refine ⟨(recoverParameter_trace_success_state_iff (input := input scanTokens 4 0 prior)).mp scan_trace, ?_, rfl⟩
  simp only [final, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- The same mandatory-consumption rule applies to an initial right parenthesis;
only the following comma is a scan stop. -/
theorem mandatory_rightParen_then_comma_stop (prior : List ParseDiagnostic) :
    recoverParameter (input commaTokens 3 0 prior) = .ok (recovered 0 1)
      (final commaTokens 3 1 (event 0 1) prior) ∧
    (final commaTokens 3 1 (event 0 1) prior).peek? = some (symbol 1 2 .comma) :=
  ⟨(recoverParameter_trace_success_state_iff (input := input commaTokens 3 0 prior)).mp comma_trace, rfl⟩

private theorem sparse_trace : FunctionParameterRecoveryTraceParses source 99
    (remainder sparseTokens 3 0) (recovered 0 1) (remainder sparseTokens 3 1) [event 0 1] :=
  ⟨.recovered (token := symbol 0 1 .plus) ⟨by change 0 < 3; decide, rfl⟩
    (.stop (.missingToken (by change 1 < 3; decide) rfl)), rfl⟩

private theorem sparse_rejection : FunctionParameterRecoveryTraceRejects source 99
    (remainder sparseTokens 3 1) (remainder sparseTokens 3 1) missingFailure.toDiagnostic [] :=
  ⟨.missingToken (by change 1 < 3; decide) rfl,
    .reported (.missingToken (by change 1 < 3; decide) rfl), rfl⟩

/-- Missing backing inside the numeric window ends an established scan, but
rejects if recovery has not yet obtained its mandatory first token. -/
theorem missing_backing_stop_versus_initial_rejection (prior : List ParseDiagnostic) :
    recoverParameter (input sparseTokens 3 0 prior) = .ok (recovered 0 1)
      (final sparseTokens 3 1 (event 0 1) prior) ∧
    recoverParameter (input sparseTokens 3 1 prior) = .reject missingFailure (input sparseTokens 3 1 prior) ∧
    (input sparseTokens 3 1 prior).cursor < (input sparseTokens 3 1 prior).window.endIndex ∧
    (input sparseTokens 3 1 prior).peek? = none ∧
    (input sparseTokens 3 1 prior).diagnostics = prior := by
  refine ⟨(recoverParameter_trace_success_state_iff (input := input sparseTokens 3 0 prior)).mp sparse_trace,
    (recoverParameter_trace_reject_failure_state_iff (input := input sparseTokens 3 1 prior)).mp sparse_rejection,
    by change 1 < 3; decide, rfl, ?_⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

/-- A window end likewise rejects without consuming a hidden backing token. -/
theorem hidden_first_token_rejects_unchanged (prior : List ParseDiagnostic) :
    (input sparseTokens 0 0 prior).tokens[0]? = some (symbol 0 1 .plus) ∧
    recoverParameter (input sparseTokens 0 0 prior) = .reject missingFailure (input sparseTokens 0 0 prior) := by
  refine ⟨rfl, (recoverParameter_trace_reject_failure_state_iff (input := input sparseTokens 0 0 prior)
    (after := remainder sparseTokens 0 0) (failure := missingFailure) (trace := [])).mp ?_⟩
  exact ⟨.windowEnd (by change 0 ≤ 0; decide), .reported (.windowEnd (by change 0 ≤ 0; decide)), rfl⟩

/-- Standalone recovery appends only its own event to an already committed
original failure. The original complete report is neither replayed nor removed. -/
theorem committed_failure_is_not_reemitted (prior : List ParseDiagnostic) (original : Failure) :
    recoverParameter (input scanTokens 4 0 (prior ++ [original.toDiagnostic])) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) (prior ++ [original.toDiagnostic])) ∧
    (final scanTokens 4 2 (event 0 4) (prior ++ [original.toDiagnostic])).diagnostics =
      prior ++ [original.toDiagnostic, event 0 4] := by
  have result := mandatory_comma_then_rightParen_stop (prior ++ [original.toDiagnostic])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

theorem recovery_event_kept_when_not_suppressed (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical (span 0 4)) :
    ParseDiagnosticCascadeFilters text lexical [event 0 4] [event 0 4] :=
  scan_trace.cascade_kept text lexical retained

theorem recovery_event_dropped_when_suppressed (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical (span 0 4)) :
    ParseDiagnosticCascadeFilters text lexical [event 0 4] [] :=
  scan_trace.cascade_dropped text lexical suppressed

/-- Concrete filtering shows why a recovery event cannot use an unconditional
protected-suffix theorem: a matching lexical range removes it. -/
theorem recovery_event_is_conditionally_filtered (text : String) :
    filterParseDiagnostics { id := source, content := text } [] [event 0 4] = [event 0 4] ∧
    filterParseDiagnostics { id := source, content := text }
      [{ span := span 0 4, kind := .invalidToken }] [event 0 4] = [] := by
  constructor
  · exact filterParseDiagnostics_eq_of_cascadeFilters _ _
      (recovery_event_kept_when_not_suppressed text [] (by simp [LexicalCascadeSuppresses]))
  · exact filterParseDiagnostics_eq_of_cascadeFilters _ _
      (recovery_event_dropped_when_suppressed text [span 0 4]
        ⟨span 0 4, by simp, ⟨rfl, .inl rfl⟩⟩)

end Solcore.Test.SyntaxParameterRecoveryTraceProperties
