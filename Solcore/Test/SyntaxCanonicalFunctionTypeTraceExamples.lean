import Solcore.Syntax.Parser.FunctionTypeSuccessTraceProperties
import Solcore.Syntax.Parser.FunctionTypeRejectionTraceProperties
import Solcore.Syntax.Parser.FunctionReturnsRejectionTraceProperties
import Solcore.Test.SyntaxCheckedTypeListTraceSupport
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

/-! Real type children emit parameter events before return events. Canonical
success and return-list rejection retain every AST span, full state, and prior
event; neither case assumes general recursive diagnostic-trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalFunctionTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeFunctionInternals
open Solcore.Test.SyntaxCheckedTypeListTraceSupport

private def source : SourceId := { origin := .main, path := "canonical-function-type-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 0 8, value := .keyword .functionKw }
private def returnsMarker : Token := { span := span 15 22, value := .identifier "returns" }
private def nameA : Identifier := { span := span 9 12, value := "a-b" }
private def nameC : Identifier := { span := span 23 26, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def ty (name : Identifier) : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tailToken (first : Nat) : Token := { span := span first (first + 4), value := .identifier "tail" }
private def prefixTokens : List Token := [marker, sym 8 9 .leftParen, nameToken nameA,
  sym 12 13 .comma, sym 13 14 .rightParen, returnsMarker, sym 22 23 .leftParen, nameToken nameC]
private def successText : String := "function(a-b,) returns(c-d,) tail"
private def successTokens : List Token := prefixTokens ++ [sym 26 27 .comma, sym 27 28 .rightParen, tailToken 29]
private def rejectedText : String := "function(a-b,) returns(c-d +) tail"
private def rejectedTokens : List Token := prefixTokens ++ [sym 27 28 .plus, sym 28 29 .rightParen, tailToken 30]
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}
private def parameters : DelimitedList TypeExpr := { span := span 8 14, elements := [ty nameA] }
private def returns : DelimitedList TypeExpr := { span := span 22 28, elements := [ty nameC] }
private def value : TypeExpr := {
  span := span 0 28, value := .function (span 0 8) parameters (some returns)
}

private theorem parameter_exec (content : String) (suffix : List Token) (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr
      (state content (prefixTokens ++ suffix) prior 1 []) =
      .ok parameters (state content (prefixTokens ++ suffix) prior 5 [event nameA]) := by
  apply singleton_trailing_checked_type_list (name := nameA) (trace := [event nameA])
    (openingSpan := span 8 9) (commaSpan := span 12 13) (closingSpan := span 13 14)
  · exact ⟨by change 1 < (prefixTokens ++ suffix).length; simp [prefixTokens], rfl⟩
  · exact ⟨by change 2 < (prefixTokens ++ suffix).length; simp [prefixTokens], rfl⟩
  · exact ⟨by change 3 < (prefixTokens ++ suffix).length; simp [prefixTokens], rfl⟩
  · exact ⟨by change 4 < (prefixTokens ++ suffix).length; simp [prefixTokens], rfl⟩
  · exact .hyphen (by unfold IdentifierHyphenSpelling nameA; decide)
  · decide
  · decide

private theorem success_exec (prior : List ParseDiagnostic) :
    parseFunctionType typeExpr (state successText successTokens prior 0 []) =
      .ok value (state successText successTokens prior 10 [event nameA, event nameC]) := by
  let s := state successText successTokens prior
  have keywordResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 8)
    ⟨⟨by change 0 < 11; decide, rfl⟩, rfl⟩
  have parameterResult := parameter_exec successText [sym 26 27 .comma, sym 27 28 .rightParen, tailToken 29] prior
  have listResult : delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr
      (s 6 [event nameA]) = .ok returns (s 10 [event nameA, event nameC]) := by
    apply singleton_trailing_checked_type_list (name := nameC) (trace := [event nameC])
      (openingSpan := span 22 23) (commaSpan := span 26 27) (closingSpan := span 27 28)
    · exact ⟨by change 6 < 11; decide, rfl⟩
    · exact ⟨by change 7 < 11; decide, rfl⟩
    · exact ⟨by change 8 < 11; decide, rfl⟩
    · exact ⟨by change 9 < 11; decide, rfl⟩
    · exact .hyphen (by unfold IdentifierHyphenSpelling nameC; decide)
    · decide
    · decide
  have reduced := parseFunctionReturns_eq_of_present typeExpr
    (input := s 5 [event nameA]) (after := (s 6 [event nameA]).declarativeRemainder) (span := span 15 22)
    ⟨⟨by change 5 < 11; decide, rfl⟩, rfl⟩
  have returnResult : parseFunctionReturns typeExpr (s 5 [event nameA]) =
      .ok (some returns) (s 10 [event nameA, event nameC]) := by
    rw [reduced]
    change (match delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 6 [event nameA]) with
      | .ok values output => Reply.ok (some values) output
      | .reject failure rejected => Reply.reject failure rejected
      | .invariant error => Reply.invariant error) = _
    rw [listResult]
  exact parseFunctionType_success_iff_components.mpr
    ⟨_, _, _, _, _, keywordResult, parameterResult, returnResult, rfl⟩

private def failure : Failure := {
  span := span 27 28, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .typeExpr
}

private theorem rejected_exec (prior : List ParseDiagnostic) :
    parseFunctionType typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 8 [event nameA, event nameC]) := by
  let s := state rejectedText rejectedTokens prior
  have keywordResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 8)
    ⟨⟨by change 0 < 11; decide, rfl⟩, rfl⟩
  have parameterResult := parameter_exec rejectedText [sym 27 28 .plus, sym 28 29 .rightParen, tailToken 30] prior
  have returnMarkerResult := contextual_eq_ok_of_exactTokenParses .returns .typeExpr
    (input := s 5 [event nameA]) (after := (s 6 [event nameA]).declarativeRemainder) (span := span 15 22)
    ⟨⟨by change 5 < 11; decide, rfl⟩, rfl⟩
  have listResult : delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr
      (s 6 [event nameA]) = .reject failure (s 8 [event nameA, event nameC]) := by
    apply checked_type_list_missing_separator (name := nameC) (trace := [event nameC])
    · exact ⟨by change 6 < 11; decide, rfl⟩
    · exact ⟨by change 7 < 11; decide, rfl⟩
    · exact ⟨by change 8 < 11; decide, rfl⟩
    · exact .hyphen (by unfold IdentifierHyphenSpelling nameC; decide)
    · decide
    · decide
  have returnsResult := parseFunctionReturns_reject_iff_list.mpr ⟨_, returnMarkerResult, listResult⟩
  exact parseFunctionType_reject_iff_components.mpr
    (.inr (.inr ⟨_, _, _, _, keywordResult, parameterResult, returnsResult⟩))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
theorem canonical_lexing :
    Lexer.lex (file successText) = .ok (carrier successTokens) ∧
    Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  constructor
  all_goals apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  all_goals decide +kernel

theorem canonical_parameter_then_return_events (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseFunctionType typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = state successText successTokens prior 10 [event nameA, event nameC] ∧
      output.diagnostics = prior ++ [event nameA, event nameC] ∧
      output.window = { endIndex := 11, endByte := 33 } ∧ output.peek? = some (tailToken 29) := by
  refine ⟨_, _, canonical_lexing.1, success_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem canonical_return_failure_keeps_parameter_events (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseFunctionType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 8 [event nameA, event nameC] ∧
      output.diagnostics = prior ++ [event nameA, event nameC] ∧
      output.window = { endIndex := 11, endByte := 34 } ∧ output.peek? = some (sym 27 28 .plus) ∧
      output.tokens[10]? = some (tailToken 30) ∧
      failure.expected.toList = [.symbol .comma, .symbol .rightParen] := by
  refine ⟨_, _, canonical_lexing.2, rejected_exec prior, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalFunctionTypeTraceExamples
