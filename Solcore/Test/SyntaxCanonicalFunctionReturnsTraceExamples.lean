import Solcore.Syntax.Parser.FunctionReturnsTraceProperties
import Solcore.Syntax.Parser.FunctionReturnsRejectionTraceProperties
import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples
import Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

/-! Canonical optional function returns execute real typeExpr leaves. The
empty list bypasses any supplied child; successful and rejected checked names
retain exact parent spans, full states, windows, and following source tokens. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalFunctionReturnsTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeFunctionInternals
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

private def source : SourceId := { origin := .main, path := "canonical-function-returns-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 0 7, value := .identifier "returns" }
private def name : Identifier := { span := span 8 11, value := "a-b" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def ty : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tailToken (first : Nat) : Token := { span := span first (first + 4), value := .identifier "tail" }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}
private def emptyText : String := "returns() tail"
private def emptyTokens : List Token := [marker, sym 7 8 .leftParen, sym 8 9 .rightParen, tailToken 10]
private def successText : String := "returns(a-b,) tail"
private def successTokens : List Token := [marker, sym 7 8 .leftParen, nameToken,
  sym 11 12 .comma, sym 12 13 .rightParen, tailToken 14]
private def rejectedText : String := "returns(a-b +) tail"
private def rejectedTokens : List Token := [marker, sym 7 8 .leftParen, nameToken,
  sym 12 13 .plus, sym 13 14 .rightParen, tailToken 15]

private theorem checked_child (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (token : TokenAt tokens.toArray tokens.length 2 nameToken)
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol .dot))
    (noArgs : TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol .less)) :
    typeExpr (state content tokens prior 2 []) = .ok ty (state content tokens prior 3 [event]) :=
  checked_name_type token (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
    noDot noArgs (by decide) (by decide)

private theorem empty_exec (nested : Parser TypeExpr) (prior : List ParseDiagnostic) :
    parseFunctionReturns nested (state emptyText emptyTokens prior 0 []) =
      .ok (some { span := span 7 9, elements := [] }) (state emptyText emptyTokens prior 3 []) := by
  let s := state emptyText emptyTokens prior
  have reduced := parseFunctionReturns_eq_of_present nested
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 7)
    ⟨⟨by change 0 < 4; decide, rfl⟩, rfl⟩
  have values := empty_list_bypasses_any_child nested .leftParen .rightParen .typeExpr .typeExpr
    (input := s 1 []) (afterOpening := (s 2 []).declarativeRemainder)
    (after := (s 3 []).declarativeRemainder) (openingSpan := span 7 8) (closingSpan := span 8 9)
    ⟨⟨by change 1 < 4; decide, rfl⟩, rfl⟩ ⟨⟨by change 2 < 4; decide, rfl⟩, rfl⟩
  rw [reduced]
  change (match delimited .leftParen .rightParen true nested .typeExpr .typeExpr (s 1 []) with
    | .ok values output => Reply.ok (some values) output
    | .reject failure rejected => Reply.reject failure rejected
    | .invariant error => Reply.invariant error) = _
  rw [values]
  rfl

private theorem success_exec (prior : List ParseDiagnostic) :
    parseFunctionReturns typeExpr (state successText successTokens prior 0 []) =
      .ok (some { span := span 7 13, elements := [ty] }) (state successText successTokens prior 5 [event]) := by
  let s := state successText successTokens prior
  have reduced := parseFunctionReturns_eq_of_present typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 7)
    ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have child := checked_child successText successTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
  have opening := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 7 8)
    ⟨⟨by change 1 < 6; decide, rfl⟩, rfl⟩
  have tail := trailing_close_bypasses_any_child typeExpr (sym 7 8 .leftParen) .rightParen
    .typeExpr .typeExpr 4 [ty] (input := s 3 [event])
    (afterComma := (s 4 [event]).declarativeRemainder) (after := (s 5 [event]).declarativeRemainder)
    (commaSpan := span 11 12) (closingSpan := span 12 13)
    ⟨⟨by change 3 < 6; decide, rfl⟩, rfl⟩ ⟨⟨by change 4 < 6; decide, rfl⟩, rfl⟩
  change symbol .leftParen .typeExpr (s 1 []) = .ok (sym 7 8 .leftParen) (s 2 []) at opening
  have guard : isSymbol (s 2 []) .rightParen = false := rfl
  have values : delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 1 []) =
      .ok { span := span 7 13, elements := [ty] } (s 5 [event]) := by
    dsimp only [s] at opening guard ⊢
    simp only [delimited, delimitedWithPolicy, opening, Bool.true_and, guard, Bool.false_eq_true, if_false, child]
    exact tail
  rw [reduced]
  change (match delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 1 []) with
    | .ok values output => Reply.ok (some values) output
    | .reject failure rejected => Reply.reject failure rejected
    | .invariant error => Reply.invariant error) = _
  rw [values]

private def failure : Failure := {
  span := span 12 13, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .typeExpr
}

private theorem rejected_exec (prior : List ParseDiagnostic) :
    parseFunctionReturns typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 3 [event]) := by
  let s := state rejectedText rejectedTokens prior
  have markerResult := contextual_eq_ok_of_exactTokenParses .returns .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 7)
    ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have child := checked_child rejectedText rejectedTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
  have opening := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 7 8)
    ⟨⟨by change 1 < 6; decide, rfl⟩, rfl⟩
  change symbol .leftParen .typeExpr (s 1 []) = .ok (sym 7 8 .leftParen) (s 2 []) at opening
  have guard : isSymbol (s 2 []) .rightParen = false := rfl
  have noComma : isSymbol (s 3 [event]) .comma = false := rfl
  have noClose : isSymbol (s 3 [event]) .rightParen = false := rfl
  have report : rejectAt (α := DelimitedList TypeExpr) (s 3 [event])
      { head := .symbol .comma, tail := [.symbol .rightParen] } .typeExpr = .reject failure (s 3 [event]) := rfl
  apply parseFunctionReturns_reject_iff_list.mpr
  refine ⟨_, markerResult, ?_⟩
  change delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 1 []) = _
  dsimp only [s] at opening guard noComma noClose report ⊢
  simp only [delimited, delimitedWithPolicy, opening, Bool.true_and, guard, Bool.false_eq_true, if_false, child]
  change afterDelimitedElement typeExpr .rightParen true .typeExpr .typeExpr (sym 7 8 .leftParen)
    (4 + 1) [ty] (s 3 [event]) = _
  dsimp only [s]
  simp only [afterDelimitedElement, noComma, noClose, Bool.false_eq_true, if_false, report]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem canonical_lexing :
    Lexer.lex (file emptyText) = .ok (carrier emptyTokens) ∧
    Lexer.lex (file successText) = .ok (carrier successTokens) ∧
    Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  repeat' constructor
  all_goals apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  all_goals decide +kernel

theorem canonical_empty_returns (nested : Parser TypeExpr) (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file emptyText) = .ok lexed ∧
      parseFunctionReturns nested { State.initial (file emptyText) lexed with diagnosticsRev := prior.reverse } =
        .ok (some { span := span 7 9, elements := [] }) output ∧
      output = state emptyText emptyTokens prior 3 [] ∧ output.diagnostics = prior ∧
      output.window = { endIndex := 4, endByte := 14 } ∧ output.peek? = some (tailToken 10) := by
  refine ⟨_, _, canonical_lexing.1, empty_exec nested prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_reverse, List.reverse_nil, List.nil_append]

theorem canonical_singleton_trailing_returns (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseFunctionReturns typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok (some { span := span 7 13, elements := [ty] }) output ∧
      output = state successText successTokens prior 5 [event] ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 6, endByte := 18 } ∧ output.peek? = some (tailToken 14) := by
  refine ⟨_, _, canonical_lexing.2.1, success_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem canonical_missing_separator (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseFunctionReturns typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 3 [event] ∧
      output.diagnostics = prior ++ [event] ∧ output.window = { endIndex := 6, endByte := 19 } ∧
      output.peek? = some (sym 12 13 .plus) ∧ output.tokens[5]? = some (tailToken 15) ∧
      failure.expected.toList = [.symbol .comma, .symbol .rightParen] := by
  refine ⟨_, _, canonical_lexing.2.2, rejected_exec prior, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalFunctionReturnsTraceExamples
