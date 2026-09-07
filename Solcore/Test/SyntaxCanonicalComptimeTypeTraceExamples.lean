import Solcore.Syntax.Parser.ComptimeTypeSuccessTraceProperties
import Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties
import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

/-! Canonical comptime types execute the real typeExpr child. Success and
closing rejection preserve its checked spelling event after every prior event,
with exact outer/angle spans, complete states, and untouched following tokens.
These concrete cases do not assume general recursive type trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalComptimeTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties

private def source : SourceId := { origin := .main, path := "canonical-comptime-type-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 0 8, value := .identifier "comptime" }
private def name : Identifier := { span := span 9 12, value := "a-b" }
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

private theorem child_exec (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (token : TokenAt tokens.toArray tokens.length 2 nameToken)
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol .dot))
    (noArguments : TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol .less)) :
    typeExpr (state content tokens prior 2 []) = .ok inner (state content tokens prior 3 [event]) :=
  checked_name_type (input := state content tokens prior 2 []) token
    (.hyphen (by unfold IdentifierHyphenSpelling name; decide)) noDot noArguments (by decide) (by decide)

private def successText : String := "comptime<a-b> tail"
private def successTokens : List Token := [marker, sym 8 9 .less, nameToken, sym 12 13 .greater,
  { span := span 14 18, value := .identifier "tail" }]
private def value : TypeExpr := {
  span := span 0 13, value := .comptime (span 0 8) (span 8 13) inner
}

private theorem success_exec (prior : List ParseDiagnostic) :
    parseComptimeType typeExpr (state successText successTokens prior 0 []) =
      .ok value (state successText successTokens prior 4 [event]) := by
  let s := state successText successTokens prior
  have child := child_exec successText successTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
  have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 8)
    ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 8 9)
    ⟨⟨by change 1 < 5; decide, rfl⟩, rfl⟩
  have closingResult := symbol_eq_ok_of_exactTokenParses .greater .typeExpr
    (input := s 3 [event]) (after := (s 4 [event]).declarativeRemainder) (span := span 12 13)
    ⟨⟨by change 3 < 5; decide, rfl⟩, rfl⟩
  exact parseComptimeType_success_iff_components.mpr
    ⟨marker, s 1 [], sym 8 9 .less, s 2 [], inner, s 3 [event], sym 12 13 .greater,
      markerResult, openingResult, child, closingResult, rfl⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem comptime_type_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_comptime_type (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseComptimeType typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = state successText successTokens prior 4 [event] ∧
      output.declarativeRemainder = remainder successTokens 4 ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 5, endByte := 18 } ∧
      output.peek? = some { span := span 14 18, value := .identifier "tail" } := by
  refine ⟨carrier successTokens, _, comptime_type_lexes, success_exec prior, rfl, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

private def rejectedText : String := "comptime<a-b +> tail"
private def rejectedTokens : List Token := [marker, sym 8 9 .less, nameToken,
  sym 13 14 .plus, sym 14 15 .greater, { span := span 16 20, value := .identifier "tail" }]
private def failure : Failure := {
  span := span 13 14, found := some (.symbol .plus)
  expected := { head := .symbol .greater, tail := [] }, context := .typeExpr
}

private theorem rejection_exec (prior : List ParseDiagnostic) :
    parseComptimeType typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 3 [event]) := by
  let s := state rejectedText rejectedTokens prior
  have child := child_exec rejectedText rejectedTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
  have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 8)
    ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 8 9)
    ⟨⟨by change 1 < 6; decide, rfl⟩, rfl⟩
  have missing : TokenKindAbsentAt (s 3 [event]).tokens (s 3 [event]).window.endIndex
      (s 3 [event]).cursor (.symbol .greater) := by
    simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, rejectedTokens, sym]
  have reported : RejectAtReports (s 3 [event]).file.id (s 3 [event]).window.endByte
      { head := .symbol .greater, tail := [] } .typeExpr (s 3 [event]).declarativeRemainder failure.toDiagnostic :=
    .reported (.token (current := sym 13 14 .plus) ⟨by change 3 < 6; decide, rfl⟩)
  exact missing_closing_keeps_complete_child_state typeExpr markerResult openingResult child missing reported

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem rejected_comptime_type_lexes : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_comptime_closing_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseComptimeType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 3 [event] ∧
      output.declarativeRemainder = remainder rejectedTokens 3 ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 6, endByte := 20 } ∧ output.peek? = some (sym 13 14 .plus) ∧
      output.tokens[5]? = some { span := span 16 20, value := .identifier "tail" } := by
  refine ⟨carrier rejectedTokens, _, rejected_comptime_type_lexes, rejection_exec prior, rfl, rfl, ?_, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalComptimeTypeTraceExamples
