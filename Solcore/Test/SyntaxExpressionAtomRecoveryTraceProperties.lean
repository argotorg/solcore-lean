import Solcore.Syntax.Parser.ExpressionAtomRecoveryTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties

/-! Standalone recovery consumes its mandatory first token before testing a
boundary. Independent scans drive complete replies, including malformed token
windows; recovery events have conditional, not protected, cascade behavior. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomRecoveryTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "atom-recovery-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def symbol (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def skipped : Token := { span := span 1 4, value := .identifier "a-b" }
private def elseToken (startByte endByte : Nat) : Token := { span := span startByte endByte, value := .keyword .elseKw }
private def scanTokens : List Token := [symbol 0 1 .semicolon, skipped, elseToken 4 8, symbol 8 9 .plus]
private def semicolonTokens : List Token := [elseToken 0 4, symbol 4 5 .semicolon, symbol 5 6 .plus]
private def sparseTokens : List Token := [symbol 0 1 .plus]
private def remainder (tokens : List Token) (endIndex cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex, cursor
}
private def input (tokens : List Token) (endIndex cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def recovered (startByte endByte : Nat) : Expr := {
  span := span startByte endByte, value := .error
}
private def event (startByte endByte : Nat) : ParseDiagnostic := expressionAtomRecoveryTraceEvent (span startByte endByte)
private def final (tokens : List Token) (endIndex cursor : Nat) (diagnostic : ParseDiagnostic)
    (prior : List ParseDiagnostic) : State := {
  input tokens endIndex cursor prior with diagnosticsRev := diagnostic :: prior.reverse
}
private def missingFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .expression, tail := [] }, context := .expression
}

private theorem scan_trace : ExpressionAtomRecoveryTraceParses source 99
    (remainder scanTokens 4 0) (recovered 0 4) (remainder scanTokens 4 2) [event 0 4] := by
  have continues : ¬ ExpressionAtomRecoveryStops (remainder scanTokens 4 1) (remainder scanTokens 4 1) := by
    intro stops
    cases stops <;> simp_all [TokenAt, remainder, scanTokens, skipped]
  refine ⟨.recovered (token := symbol 0 1 .semicolon) ⟨by change 0 < 4; decide, rfl⟩ ?_, rfl⟩
  exact .next continues (token := skipped) ⟨by change 1 < 4; decide, rfl⟩
    (.stop (.elseKeyword ⟨by change 2 < 4; decide, rfl⟩))

private theorem semicolon_trace : ExpressionAtomRecoveryTraceParses source 99
    (remainder semicolonTokens 3 0) (recovered 0 4) (remainder semicolonTokens 3 1) [event 0 4] :=
  ⟨.recovered (token := elseToken 0 4) ⟨by change 0 < 3; decide, rfl⟩
    (.stop (.semicolon ⟨by change 1 < 3; decide, rfl⟩)), rfl⟩

/-- Initial semicolon is consumed, the intervening hyphen identifier is skipped
without checking it, and the later else keyword is left unread. -/
theorem mandatory_semicolon_then_else_stop (prior : List ParseDiagnostic) :
    recoverAtom (input scanTokens 4 0 prior) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) prior) ∧
    (final scanTokens 4 2 (event 0 4) prior).diagnostics = prior ++ [event 0 4] ∧
    (final scanTokens 4 2 (event 0 4) prior).peek? = some (elseToken 4 8) := by
  refine ⟨(recoverAtom_trace_success_state_iff (input := input scanTokens 4 0 prior)).mp scan_trace, ?_, rfl⟩
  simp only [final, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- Even an initial else keyword is consumed; only the following semicolon
is a scan stop. -/
theorem mandatory_else_then_semicolon_stop (prior : List ParseDiagnostic) :
    recoverAtom (input semicolonTokens 3 0 prior) = .ok (recovered 0 4)
      (final semicolonTokens 3 1 (event 0 4) prior) ∧
    (final semicolonTokens 3 1 (event 0 4) prior).peek? = some (symbol 4 5 .semicolon) :=
  ⟨(recoverAtom_trace_success_state_iff (input := input semicolonTokens 3 0 prior)).mp semicolon_trace, rfl⟩

private theorem sparse_trace : ExpressionAtomRecoveryTraceParses source 99
    (remainder sparseTokens 3 0) (recovered 0 1) (remainder sparseTokens 3 1) [event 0 1] :=
  ⟨.recovered (token := symbol 0 1 .plus) ⟨by change 0 < 3; decide, rfl⟩
    (.stop (.missingToken (by change 1 < 3; decide) rfl)), rfl⟩

private theorem sparse_rejection : ExpressionAtomRecoveryTraceRejects source 99
    (remainder sparseTokens 3 1) (remainder sparseTokens 3 1) missingFailure.toDiagnostic [] :=
  ⟨.missingToken (by change 1 < 3; decide) rfl,
    .reported (.missingToken (by change 1 < 3; decide) rfl), rfl⟩

/-- Missing backing inside the numeric window ends an established scan, but
rejects if recovery has not yet obtained its mandatory first token. -/
theorem missing_backing_stop_versus_initial_rejection (prior : List ParseDiagnostic) :
    recoverAtom (input sparseTokens 3 0 prior) = .ok (recovered 0 1)
      (final sparseTokens 3 1 (event 0 1) prior) ∧
    recoverAtom (input sparseTokens 3 1 prior) = .reject missingFailure (input sparseTokens 3 1 prior) ∧
    (input sparseTokens 3 1 prior).cursor < (input sparseTokens 3 1 prior).window.endIndex ∧
    (input sparseTokens 3 1 prior).peek? = none ∧
    (input sparseTokens 3 1 prior).diagnostics = prior := by
  refine ⟨(recoverAtom_trace_success_state_iff (input := input sparseTokens 3 0 prior)).mp sparse_trace,
    (recoverAtom_trace_reject_failure_state_iff (input := input sparseTokens 3 1 prior)).mp sparse_rejection,
    by change 1 < 3; decide, rfl, ?_⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

/-- A window end likewise rejects without consuming a hidden backing token. -/
theorem hidden_first_token_rejects_unchanged (prior : List ParseDiagnostic) :
    (input sparseTokens 0 0 prior).tokens[0]? = some (symbol 0 1 .plus) ∧
    recoverAtom (input sparseTokens 0 0 prior) = .reject missingFailure (input sparseTokens 0 0 prior) := by
  refine ⟨rfl, (recoverAtom_trace_reject_failure_state_iff (input := input sparseTokens 0 0 prior)
    (after := remainder sparseTokens 0 0) (failure := missingFailure) (trace := [])).mp ?_⟩
  exact ⟨.windowEnd (by change 0 ≤ 0; decide), .reported (.windowEnd (by change 0 ≤ 0; decide)), rfl⟩

/-- After the mandatory token, an active window end stops before a still-backed
identifier. Its hidden spelling is neither consumed nor checked. -/
theorem active_window_hides_next_token (prior : List ParseDiagnostic) :
    recoverAtom (input scanTokens 1 0 prior) = .ok (recovered 0 1)
      (final scanTokens 1 1 (event 0 1) prior) ∧
    (final scanTokens 1 1 (event 0 1) prior).tokens[1]? = some skipped ∧
    (final scanTokens 1 1 (event 0 1) prior).peek? = none := by
  refine ⟨(recoverAtom_trace_success_state_iff (input := input scanTokens 1 0 prior)
    (value := recovered 0 1) (after := remainder scanTokens 1 1) (trace := [event 0 1])).mp ?_, rfl, rfl⟩
  exact ⟨.recovered (token := symbol 0 1 .semicolon) ⟨by change 0 < 1; decide, rfl⟩
    (.stop (.windowEnd (by change 1 ≤ 1; decide))), rfl⟩

/-- Standalone recovery appends only its own event to an already committed
original failure. The original complete report is neither replayed nor removed. -/
theorem committed_failure_is_not_reemitted (prior : List ParseDiagnostic) (original : Failure) :
    recoverAtom (input scanTokens 4 0 (prior ++ [original.toDiagnostic])) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) (prior ++ [original.toDiagnostic])) ∧
    (final scanTokens 4 2 (event 0 4) (prior ++ [original.toDiagnostic])).diagnostics =
      prior ++ [original.toDiagnostic, event 0 4] := by
  have result := mandatory_semicolon_then_else_stop (prior ++ [original.toDiagnostic])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

theorem duplicate_prior_events_are_not_deduplicated (prior : List ParseDiagnostic) :
    recoverAtom (input scanTokens 4 0 (prior ++ [event 0 4, event 0 4])) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) (prior ++ [event 0 4, event 0 4])) ∧
    (final scanTokens 4 2 (event 0 4) (prior ++ [event 0 4, event 0 4])).diagnostics =
      prior ++ [event 0 4, event 0 4, event 0 4] := by
  have result := mandatory_semicolon_then_else_stop (prior ++ [event 0 4, event 0 4])
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

end Solcore.Test.SyntaxExpressionAtomRecoveryTraceProperties
