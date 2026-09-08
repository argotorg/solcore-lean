import Solcore.Test.SyntaxExpressionAtomTraceSupport
import Solcore.Syntax.DeclarativeExpressionAtomTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties

/-! Independent public atom traces drive complete executable replies. The real
literal child rejects inside a dot constructor after its checked-name event.
Recovery rewinds only the cursor, commits that report once, and skips tokens
without replaying name checks. This is one atom layer, not full expressions. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals SyntaxExpressionAtomTraceSupport

private def source : SourceId := { origin := .main, path := "public-atom-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def symbol (startByte endByte : Nat) (value : Symbol) : Token := { span := span startByte endByte, value := .symbol value }
private def name : Identifier := { span := span 1 4, value := "a-b" }
private def tokens : List Token := [symbol 0 1 .dot, { span := name.span, value := .identifier name.value },
  symbol 4 5 .leftParen, symbol 5 6 .plus, symbol 6 7 .rightParen, symbol 8 9 .semicolon]
private def remainder (cursor : Nat) : Remainder := { tokens := tokens.toArray, endIndex := 6, cursor }
private def input (cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor
  window := { endIndex := 6, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def coreFailure : Failure := {
  span := span 5 6, found := some (.symbol .plus), expected := { head := .coreLiteral, tail := [] }, context := .expression
}
private def recovered : Expr := { span := span 0 6, value := .error }
private def recoveryEvent : ParseDiagnostic := expressionAtomRecoveryTraceEvent recovered.span
private def events : List ParseDiagnostic := [nameEvent, coreFailure.toDiagnostic, recoveryEvent]
private def final (prior : List ParseDiagnostic) : State := {
  input 4 prior with diagnosticsRev := events.reverse ++ prior.reverse
}

private theorem name_trace : ExpressionNameTraceParses source 99 (remainder 1) name (remainder 2) [nameEvent] :=
  .identifier (by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, remainder, tokens, name])
    (.parsed ⟨⟨by change 1 < 6; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling name; decide)))

private theorem literal_rejection : LiteralExpressionTraceRejects source 99 (remainder 3) (remainder 3)
    coreFailure.toDiagnostic [] :=
  ⟨.absent (by simp [CoreLiteralAbsentAt, TokenAt, remainder, tokens, symbol]),
    .reported (.token (current := symbol 5 6 .plus) ⟨by change 3 < 6; decide, rfl⟩), rfl⟩

private theorem core_rejection : coreRejects source 99 (remainder 0) (remainder 3) coreFailure.toDiagnostic [nameEvent] := by
  have selection : ExpressionAtomDispatchSelects (remainder 0) .dotConstructor :=
    .dotConstructor (by simp [CoreLiteralStartsAt, TokenAt, remainder, tokens, symbol])
      (by simp [ExpressionNameStartsAt, TokenAt, remainder, tokens, symbol])
      ⟨span 0 1, ⟨by change 0 < 6; decide, rfl⟩⟩
  apply ExpressionAtomDispatchTraceRejects.selected .dotConstructor selection
  change DotConstructorTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects
    source 99 (remainder 0) (remainder 3) coreFailure.toDiagnostic [nameEvent]
  simpa only [List.append_nil] using DotConstructorTraceRejects.argumentsRejected
    (input := remainder 0) (afterDot := remainder 1) (afterName := remainder 2)
    (span 0 1) ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩ name_trace
    (.present (input := remainder 2) (span 4 5) ⟨by change 2 < 6; decide, rfl⟩
      (.firstRejected (afterOpening := remainder 3) (span 4 5) ⟨⟨by change 2 < 6; decide, rfl⟩, rfl⟩
        (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens, symbol])) literal_rejection))

private theorem scan_continues {cursor : Nat} (position : cursor = 1 ∨ cursor = 2 ∨ cursor = 3) :
    ¬ ExpressionAtomRecoveryStops (remainder cursor) (remainder cursor) := by
  rcases position with rfl | rfl | rfl <;> intro stops <;>
    cases stops <;> simp_all [TokenAt, remainder, tokens, name, symbol]

private theorem recovery_trace : ExpressionAtomRecoveryTraceParses source 99 (remainder 0)
    recovered (remainder 4) [recoveryEvent] :=
  ⟨.recovered (token := symbol 0 1 .dot) ⟨by change 0 < 6; decide, rfl⟩
    (.next (scan_continues (.inl rfl)) ⟨by change 1 < 6; decide, rfl⟩
      (.next (scan_continues (.inr (.inl rfl))) ⟨by change 2 < 6; decide, rfl⟩
        (.next (scan_continues (.inr (.inr rfl))) ⟨by change 3 < 6; decide, rfl⟩
          (.stop (.rightParen ⟨by change 4 < 6; decide, rfl⟩))))), rfl⟩

private theorem nonboundary : ¬ ExpressionAtomBoundaryStops (remainder 0) := by
  intro stops
  cases stops <;> simp_all [TokenAt, remainder, tokens, symbol]

private theorem public_trace : ExpressionAtomTraceParses coreParses coreRejects source 99
    (remainder 0) recovered (remainder 4) events :=
  .recovered core_rejection nonboundary recovery_trace

/-- Core literal failure occurs after the name warning, before any recovery
report is committed. Its complete Failure is preserved. -/
theorem dot_core_failure_retains_checked_name (prior : List ParseDiagnostic) :
    expressionAtomCore literalExpression blockParser (input 0 prior) =
      .reject coreFailure { input 3 prior with diagnosticsRev := nameEvent :: prior.reverse } ∧
    ({ input 3 prior with diagnosticsRev := nameEvent :: prior.reverse } : State).diagnostics = prior ++ [nameEvent] := by
  refine ⟨core_reject_of_trace (input := input 0 prior) core_rejection, ?_⟩
  simp only [State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- Revisited and skipped name tokens are not checked again. The closing
parenthesis and following semicolon remain outside the recovered error span. -/
theorem public_dot_recovery_orders_reports (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (input 0 prior) = .ok recovered (final prior) ∧
    (final prior).diagnostics = prior ++ events ∧
    (final prior).cursor = 4 ∧ (final prior).peek? = some (symbol 6 7 .rightParen) ∧
    (final prior).tokens[5]? = some (symbol 8 9 .semicolon) := by
  refine ⟨public_success_of_trace (input := input 0 prior) public_trace, ?_, rfl, rfl, rfl⟩
  simp only [final, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem prior_duplicates_survive_recovery (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (input 0 (prior ++ [nameEvent, nameEvent])) =
      .ok recovered (final (prior ++ [nameEvent, nameEvent])) ∧
    (final (prior ++ [nameEvent, nameEvent])).diagnostics =
      prior ++ [nameEvent, nameEvent, nameEvent, coreFailure.toDiagnostic, recoveryEvent] := by
  have result := public_dot_recovery_orders_reports (prior ++ [nameEvent, nameEvent])
  exact ⟨result.1, by simpa only [events, List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

/-- A successful selected name is returned directly, even though the supplied
literal-only nested parser would reject its spelling. The next '(' is unread. -/
theorem successful_name_bypasses_recovery (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (input 1 prior) =
      .ok { span := name.span, value := .identifier name }
        { input 2 prior with diagnosticsRev := nameEvent :: prior.reverse } ∧
    ({ input 2 prior with diagnosticsRev := nameEvent :: prior.reverse } : State).peek? = some (symbol 4 5 .leftParen) := by
  have selection : ExpressionAtomDispatchSelects (remainder 1) .name :=
    .name (by simp [CoreLiteralStartsAt, TokenAt, remainder, tokens])
      (.inr (.inr ⟨name.span, name.value, ⟨by change 1 < 6; decide, rfl⟩⟩))
  have parsed : ExpressionAtomTraceParses coreParses coreRejects source 99 (remainder 1)
      { span := name.span, value := .identifier name } (remainder 2) [nameEvent] :=
    .core (.selected .name selection (.parsed name_trace))
  exact ⟨public_success_of_trace (input := input 1 prior) parsed, rfl⟩

private def boundaryFailure : Failure := {
  span := span 6 7, found := some (.symbol .rightParen), expected := { head := .expression, tail := [] }, context := .expression
}
private theorem boundary_trace : ExpressionAtomTraceRejects coreRejects source 99
    (remainder 4) (remainder 4) boundaryFailure.toDiagnostic [] := by
  have selection : ExpressionAtomDispatchSelects (remainder 4) .final := by
    apply ExpressionAtomDispatchSelects.final <;>
      simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt, remainder, tokens, symbol]
  exact .boundary (input := remainder 4) (failed := remainder 4)
    (ExpressionAtomDispatchTraceRejects.selected .final selection
      (.rejected (.reported (.token (current := symbol 6 7 .rightParen) ⟨by change 4 < 6; decide, rfl⟩))))
    (.rightParen ⟨by change 4 < 6; decide, rfl⟩)

theorem first_boundary_failure_is_uncommitted (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (input 4 prior) = .reject boundaryFailure (input 4 prior) ∧
    (input 4 prior).diagnostics = prior := by
  refine ⟨public_reject_of_trace (input := input 4 prior) boundary_trace, ?_⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

private def missingInput (prior : List ParseDiagnostic) : State := {
  input 0 prior with tokens := #[], window := { endIndex := 2, endByte := 99 }
}
private def missingFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .expression, tail := [] }, context := .expression
}
private theorem missing_trace : ExpressionAtomTraceRejects coreRejects source 99
    (missingInput []).declarativeRemainder (missingInput []).declarativeRemainder missingFailure.toDiagnostic
    [missingFailure.toDiagnostic] := by
  have selection : ExpressionAtomDispatchSelects (missingInput []).declarativeRemainder .final := by
    apply ExpressionAtomDispatchSelects.final <;>
      simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt,
        missingInput, input, State.declarativeRemainder]
  have core : coreRejects source 99 (missingInput []).declarativeRemainder
      (missingInput []).declarativeRemainder missingFailure.toDiagnostic [] :=
    .selected .final selection
      (.rejected (.reported (.missingToken (by change 0 < 2; decide) rfl)))
  have continues : ¬ ExpressionAtomBoundaryStops (missingInput []).declarativeRemainder := by
    intro stops
    cases stops <;> simp_all [TokenAt, missingInput, input, State.declarativeRemainder]
  exact .recovery core continues ⟨.missingToken (by change 0 < 2; decide) rfl,
    .reported (.missingToken (by change 0 < 2; decide) rfl), rfl⟩

/-- The core and recovery failures have equal payloads, but only the original
is committed. The second remains the exact terminal Failure. -/
theorem initial_missing_backing_separates_two_reports (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (missingInput prior) =
      .reject missingFailure { missingInput prior with diagnosticsRev := missingFailure.toDiagnostic :: prior.reverse } ∧
    ({ missingInput prior with diagnosticsRev := missingFailure.toDiagnostic :: prior.reverse } : State).diagnostics =
      prior ++ [missingFailure.toDiagnostic] ∧
    (missingInput prior).cursor < (missingInput prior).window.endIndex ∧ (missingInput prior).peek? = none := by
  refine ⟨public_reject_of_trace (input := missingInput prior) missing_trace, ?_, by change 0 < 2; decide, rfl⟩
  simp only [State.diagnostics, List.reverse_cons, List.reverse_reverse]

theorem mixed_recovery_filter_retains_name (text : String) (lexical : List SourceSpan)
    (reportSuppressed : LexicalCascadeSuppresses text lexical coreFailure.span)
    (recoverySuppressed : LexicalCascadeSuppresses text lexical recovered.span) :
    ParseDiagnosticCascadeFilters text lexical events [nameEvent] :=
  expressionAtomRecoveryTrace_cascadeFilters text lexical
    (show ParseDiagnosticCascadeFilters text lexical [nameEvent] [nameEvent] from
      .keep (fun suppressed => suppressed.1) .nil)
    (.drop ⟨by trivial, reportSuppressed⟩ .nil)
    (recovery_trace.cascade_dropped text lexical recoverySuppressed)

theorem lexical_cascade_drops_only_report_and_recovery (text : String) :
    filterParseDiagnostics { id := source, content := text }
      [{ span := span 0 6, kind := .invalidToken }] events = [nameEvent] :=
  filterParseDiagnostics_eq_of_cascadeFilters _ _
    (mixed_recovery_filter_retains_name text [span 0 6]
      ⟨span 0 6, by simp, ⟨rfl, .inr (.inl ⟨by decide, by decide⟩)⟩⟩
      ⟨span 0 6, by simp, ⟨rfl, .inl rfl⟩⟩)

end Solcore.Test.SyntaxExpressionAtomTraceProperties
