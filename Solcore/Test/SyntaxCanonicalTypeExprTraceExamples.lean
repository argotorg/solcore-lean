import Solcore.Syntax.Parser.TypeExprTraceSoundnessProperties
import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
import Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

/-! Canonical, multiply nested public type-expression executions. Component
proofs connect proxy, comptime, and the checked name leaf, then the recursive
soundness contracts supply the fuel-free trace. Existing events, complete
states, exact spans, uncommitted failures, and following tokens are retained.
Only the finite lexer examples use kernel evaluation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalTypeExprTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties

private def source : SourceId := { origin := .main, path := "canonical-type-expr-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 1 9, value := .identifier "comptime" }
private def name : Identifier := { span := span 10 13, value := "a-b" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def inner : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}

private theorem child_exec (fuel : Nat) (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (token : TokenAt tokens.toArray tokens.length 3 nameToken)
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 4 (.symbol .dot))
    (noArguments : TokenKindAbsentAt tokens.toArray tokens.length 4 (.symbol .less)) :
    typeExprWithFuel (fuel + 1) (state content tokens prior 3 []) =
      .ok inner (state content tokens prior 4 [event]) :=
  checked_name_type_with_positive_fuel fuel (input := state content tokens prior 3 []) token
    (.hyphen (by unfold IdentifierHyphenSpelling name; decide)) noDot noArguments (by decide) (by decide)

private def successText : String := "@comptime<a-b> tail"
private def successTokens : List Token := [sym 0 1 .at, marker, sym 9 10 .less, nameToken,
  sym 13 14 .greater, { span := span 15 19, value := .identifier "tail" }]
private def comptimeValue : TypeExpr := {
  span := span 1 14, value := .comptime (span 1 9) (span 9 14) inner
}
private def value : TypeExpr := { span := span 0 14, value := .proxy (span 0 1) comptimeValue }

private theorem success_with_fuel (fuel : Nat) (prior : List ParseDiagnostic) :
    typeExprWithFuel (fuel + 3) (state successText successTokens prior 0 []) =
      .ok value (state successText successTokens prior 5 [event]) := by
  let s := state successText successTokens prior
  have child := child_exec fuel successText successTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
  have proxyResult := symbol_eq_ok_of_exactTokenParses .at .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 1 9)
    ⟨⟨by change 1 < 6; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
    (input := s 2 []) (after := (s 3 []).declarativeRemainder) (span := span 9 10)
    ⟨⟨by change 2 < 6; decide, rfl⟩, rfl⟩
  have closingResult := symbol_eq_ok_of_exactTokenParses .greater .typeExpr
    (input := s 4 [event]) (after := (s 5 [event]).declarativeRemainder) (span := span 13 14)
    ⟨⟨by change 4 < 6; decide, rfl⟩, rfl⟩
  have comptimeResult : typeExprWithFuel (fuel + 2) (s 1 []) = .ok comptimeValue (s 5 [event]) := by
    rw [typeExprWithFuel_eq_raw_of_selection (fuel + 1)
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (s 1 []) = .comptime from rfl))]
    exact parseComptimeType_success_iff_components.mpr
      ⟨marker, s 2 [], sym 9 10 .less, s 3 [], inner, s 4 [event], sym 13 14 .greater,
        markerResult, openingResult, child, closingResult, rfl⟩
  rw [typeExprWithFuel_eq_raw_of_selection (fuel + 2)
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (s 0 []) = .proxy from rfl))]
  exact parseProxyType_success_iff_components.mpr
    ⟨sym 0 1 .at, s 1 [], comptimeValue, proxyResult, comptimeResult, rfl⟩

private theorem success_exec (prior : List ParseDiagnostic) :
    typeExpr (state successText successTokens prior 0 []) =
      .ok value (state successText successTokens prior 5 [event]) :=
  success_with_fuel 4 prior

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem nested_type_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_nested_type (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = state successText successTokens prior 5 [event] ∧
      output.declarativeRemainder = remainder successTokens 5 ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 6, endByte := 19 } ∧
      output.peek? = some { span := span 15 19, value := .identifier "tail" } ∧
      TypeExprTraceParses source 19 (remainder successTokens 0) value (remainder successTokens 5) [event] := by
  rcases typeExpr_trace_success_sound (success_exec prior) with ⟨trace, parsed, events⟩
  have exactEvents : (state successText successTokens prior 5 [event]).diagnostics =
      (state successText successTokens prior 0 []).diagnostics ++ [event] := by
    simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse,
      List.reverse_nil, List.nil_append]
  have same := List.append_cancel_left (events.symm.trans exactEvents)
  refine ⟨carrier successTokens, _, nested_type_lexes, success_exec prior, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]
  · have endByte : (state successText successTokens prior 0 []).window.endByte = 19 := rfl
    have sourceEq : (state successText successTokens prior 0 []).file.id = source := rfl
    have inputEq : (state successText successTokens prior 0 []).declarativeRemainder =
        remainder successTokens 0 := rfl
    have outputEq : (state successText successTokens prior 5 [event]).declarativeRemainder =
        remainder successTokens 5 := rfl
    simpa only [same, endByte, sourceEq, inputEq, outputEq] using parsed

private def rejectedText : String := "@comptime<a-b +> tail"
private def rejectedTokens : List Token := [sym 0 1 .at, marker, sym 9 10 .less, nameToken,
  sym 14 15 .plus, sym 15 16 .greater, { span := span 17 21, value := .identifier "tail" }]
private def failure : Failure := {
  span := span 14 15, found := some (.symbol .plus)
  expected := { head := .symbol .greater, tail := [] }, context := .typeExpr
}

private theorem rejection_with_fuel (fuel : Nat) (prior : List ParseDiagnostic) :
    typeExprWithFuel (fuel + 3) (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 4 [event]) := by
  let s := state rejectedText rejectedTokens prior
  have child := child_exec fuel rejectedText rejectedTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
  have proxyResult := symbol_eq_ok_of_exactTokenParses .at .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 7; decide, rfl⟩, rfl⟩
  have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 1 9)
    ⟨⟨by change 1 < 7; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
    (input := s 2 []) (after := (s 3 []).declarativeRemainder) (span := span 9 10)
    ⟨⟨by change 2 < 7; decide, rfl⟩, rfl⟩
  have missing : TokenKindAbsentAt (s 4 [event]).tokens (s 4 [event]).window.endIndex
      (s 4 [event]).cursor (.symbol .greater) := by
    simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, rejectedTokens, sym]
  have reported : RejectAtReports (s 4 [event]).file.id (s 4 [event]).window.endByte
      { head := .symbol .greater, tail := [] } .typeExpr (s 4 [event]).declarativeRemainder failure.toDiagnostic :=
    .reported (.token (current := sym 14 15 .plus) ⟨by change 4 < 7; decide, rfl⟩)
  have comptimeResult : typeExprWithFuel (fuel + 2) (s 1 []) = .reject failure (s 4 [event]) := by
    rw [typeExprWithFuel_eq_raw_of_selection (fuel + 1)
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (s 1 []) = .comptime from rfl))]
    exact missing_closing_keeps_complete_child_state (typeExprWithFuel (fuel + 1))
      markerResult openingResult child missing reported
  rw [typeExprWithFuel_eq_raw_of_selection (fuel + 2)
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (s 0 []) = .proxy from rfl))]
  exact parseProxyType_reject_iff_components.mpr (.inr ⟨sym 0 1 .at, s 1 [], proxyResult, comptimeResult⟩)

private theorem rejection_exec (prior : List ParseDiagnostic) :
    typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 4 [event]) :=
  rejection_with_fuel 5 prior

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem rejected_nested_type_lexes : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_nested_type_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 4 [event] ∧
      output.declarativeRemainder = remainder rejectedTokens 4 ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 7, endByte := 21 } ∧ output.peek? = some (sym 14 15 .plus) ∧
      output.tokens[6]? = some { span := span 17 21, value := .identifier "tail" } ∧
      TypeExprTraceRejects source 21 (remainder rejectedTokens 0) (remainder rejectedTokens 4)
        failure.toDiagnostic [event] := by
  rcases typeExpr_reject_trace_sound (rejection_exec prior) with ⟨trace, rejected, events⟩
  have exactEvents : (state rejectedText rejectedTokens prior 4 [event]).diagnostics =
      (state rejectedText rejectedTokens prior 0 []).diagnostics ++ [event] := by
    simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse,
      List.reverse_nil, List.nil_append]
  have same := List.append_cancel_left (events.symm.trans exactEvents)
  refine ⟨carrier rejectedTokens, _, rejected_nested_type_lexes, rejection_exec prior,
    rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]
  · have endByte : (state rejectedText rejectedTokens prior 0 []).window.endByte = 21 := rfl
    have sourceEq : (state rejectedText rejectedTokens prior 0 []).file.id = source := rfl
    have inputEq : (state rejectedText rejectedTokens prior 0 []).declarativeRemainder =
        remainder rejectedTokens 0 := rfl
    have outputEq : (state rejectedText rejectedTokens prior 4 [event]).declarativeRemainder =
        remainder rejectedTokens 4 := rfl
    simpa only [same, endByte, sourceEq, inputEq, outputEq] using rejected

end Solcore.Test.SyntaxCanonicalTypeExprTraceExamples
