import Solcore.Syntax.Parser.TupleTypeSuccessTraceProperties
import Solcore.Syntax.Parser.TupleTypeRejectionTraceProperties
import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples
import Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

/-! Canonical tuple types use real typeExpr children. Empty, singleton-trailing,
and two-element lists stay tuples, and a missing separator preserves earlier
checked-name events without committing the ordered comma/right-paren report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalTupleTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties
open Solcore.Syntax.Parser.DelimitedTraceInternals

private def source : SourceId := { origin := .main, path := "canonical-tuple-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def nameA : Identifier := { span := span 1 4, value := "a-b" }
private def nameC : Identifier := { span := span 5 8, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def ty (name : Identifier) : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tailToken (first : Nat) : Token := { span := span first (first + 4), value := .identifier "tail" }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}

private def emptyText : String := "() tail"
private def emptyTokens : List Token := [sym 0 1 .leftParen, sym 1 2 .rightParen, tailToken 3]
private def singleText : String := "(a-b,) tail"
private def singleTokens : List Token := [sym 0 1 .leftParen, nameToken nameA,
  sym 4 5 .comma, sym 5 6 .rightParen, tailToken 7]
private def pairText : String := "(a-b,c-d,) tail"
private def pairTokens : List Token := [sym 0 1 .leftParen, nameToken nameA,
  sym 4 5 .comma, nameToken nameC, sym 8 9 .comma, sym 9 10 .rightParen, tailToken 11]
private def rejectedText : String := "(a-b +) tail"
private def rejectedTokens : List Token := [sym 0 1 .leftParen, nameToken nameA,
  sym 5 6 .plus, sym 6 7 .rightParen, tailToken 8]

private theorem first_child (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (token : TokenAt tokens.toArray tokens.length 1 (nameToken nameA))
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 2 (.symbol .dot))
    (noArgs : TokenKindAbsentAt tokens.toArray tokens.length 2 (.symbol .less)) :
    typeExpr (state content tokens prior 1 []) =
      .ok (ty nameA) (state content tokens prior 2 [event nameA]) :=
  checked_name_type token (.hyphen (by unfold IdentifierHyphenSpelling nameA; decide))
    noDot noArgs (by decide) (by decide)

private theorem empty_exec (prior : List ParseDiagnostic) :
    parseTupleType typeExpr (state emptyText emptyTokens prior 0 []) =
      .ok { span := span 0 2, value := .tuple [] } (state emptyText emptyTokens prior 2 []) := by
  apply parseTupleType_success_iff_list.mpr
  refine ⟨{ span := span 0 2, elements := [] }, ?_, rfl⟩
  exact empty_list_bypasses_any_child typeExpr .leftParen .rightParen .typeExpr .typeExpr
    (afterOpening := (state emptyText emptyTokens prior 1 []).declarativeRemainder)
    (after := (state emptyText emptyTokens prior 2 []).declarativeRemainder)
    (openingSpan := span 0 1) (closingSpan := span 1 2)
    ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩ ⟨⟨by change 1 < 3; decide, rfl⟩, rfl⟩

private theorem single_exec (prior : List ParseDiagnostic) :
    parseTupleType typeExpr (state singleText singleTokens prior 0 []) =
      .ok { span := span 0 6, value := .tuple [ty nameA] }
        (state singleText singleTokens prior 4 [event nameA]) := by
  let s := state singleText singleTokens prior
  have child := first_child singleText singleTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, singleTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, singleTokens, sym])
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩
  have tail := trailing_close_bypasses_any_child typeExpr (sym 0 1 .leftParen) .rightParen
    .typeExpr .typeExpr 4 [ty nameA] (input := s 2 [event nameA])
    (afterComma := (s 3 [event nameA]).declarativeRemainder)
    (after := (s 4 [event nameA]).declarativeRemainder) (commaSpan := span 4 5) (closingSpan := span 5 6)
    ⟨⟨by change 2 < 5; decide, rfl⟩, rfl⟩ ⟨⟨by change 3 < 5; decide, rfl⟩, rfl⟩
  apply parseTupleType_success_iff_list.mpr
  refine ⟨{ span := span 0 6, elements := [ty nameA] }, ?_, rfl⟩
  change delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 0 []) = _
  change symbol .leftParen .typeExpr (s 0 []) = .ok (sym 0 1 .leftParen) (s 1 []) at marker
  have guard : isSymbol (s 1 []) .rightParen = false := rfl
  dsimp only [s] at marker guard
  dsimp only [s]
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, guard, Bool.false_eq_true,
    if_false, child]
  exact tail

private theorem pair_exec (prior : List ParseDiagnostic) :
    parseTupleType typeExpr (state pairText pairTokens prior 0 []) =
      .ok { span := span 0 10, value := .tuple [ty nameA, ty nameC] }
        (state pairText pairTokens prior 6 [event nameA, event nameC]) := by
  let s := state pairText pairTokens prior
  have first := first_child pairText pairTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, pairTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, pairTokens, sym])
  have second : typeExpr (s 3 [event nameA]) = .ok (ty nameC) (s 4 [event nameA, event nameC]) :=
    checked_name_type (name := nameC) ⟨by change 3 < 7; decide, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling nameC; decide))
      (by simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, pairTokens, sym])
      (by simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, pairTokens, sym])
      (by decide) (by decide)
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 7; decide, rfl⟩, rfl⟩
  have comma := symbol_eq_ok_of_exactTokenParses .comma .typeExpr
    (input := s 2 [event nameA]) (after := (s 3 [event nameA]).declarativeRemainder) (span := span 4 5)
    ⟨⟨by change 2 < 7; decide, rfl⟩, rfl⟩
  have tail := trailing_close_bypasses_any_child typeExpr (sym 0 1 .leftParen) .rightParen
    .typeExpr .typeExpr 5 [ty nameC, ty nameA] (input := s 4 [event nameA, event nameC])
    (afterComma := (s 5 [event nameA, event nameC]).declarativeRemainder)
    (after := (s 6 [event nameA, event nameC]).declarativeRemainder)
    (commaSpan := span 8 9) (closingSpan := span 9 10)
    ⟨⟨by change 4 < 7; decide, rfl⟩, rfl⟩ ⟨⟨by change 5 < 7; decide, rfl⟩, rfl⟩
  change symbol .leftParen .typeExpr (s 0 []) = .ok (sym 0 1 .leftParen) (s 1 []) at marker
  change symbol .comma .typeExpr (s 2 [event nameA]) = .ok (sym 4 5 .comma) (s 3 [event nameA]) at comma
  have noCloseFirst : isSymbol (s 1 []) .rightParen = false := rfl
  have hasComma : isSymbol (s 2 [event nameA]) .comma = true := rfl
  have noCloseSecond : isSymbol (s 3 [event nameA]) .rightParen = false := rfl
  dsimp only [s] at marker comma second noCloseFirst hasComma noCloseSecond
  apply parseTupleType_success_iff_list.mpr
  refine ⟨{ span := span 0 10, elements := [ty nameA, ty nameC] }, ?_, rfl⟩
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, noCloseFirst,
    Bool.false_eq_true, if_false, first]
  change afterDelimitedElement typeExpr .rightParen true .typeExpr .typeExpr (sym 0 1 .leftParen)
    (6 + 1) [ty nameA] (s 2 [event nameA]) = _
  dsimp only [s]
  simp only [afterDelimitedElement, hasComma, if_true, comma, Bool.true_and,
    noCloseSecond, Bool.false_eq_true, if_false, second]
  exact tail

private def failure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .typeExpr
}

private theorem rejected_exec (prior : List ParseDiagnostic) :
    parseTupleType typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 2 [event nameA]) := by
  let s := state rejectedText rejectedTokens prior
  have child := first_child rejectedText rejectedTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩
  change symbol .leftParen .typeExpr (s 0 []) = .ok (sym 0 1 .leftParen) (s 1 []) at marker
  have guard : isSymbol (s 1 []) .rightParen = false := rfl
  have noComma : isSymbol (s 2 [event nameA]) .comma = false := rfl
  have noClose : isSymbol (s 2 [event nameA]) .rightParen = false := rfl
  have report : rejectAt (α := DelimitedList TypeExpr) (s 2 [event nameA])
      { head := .symbol .comma, tail := [.symbol .rightParen] }
      .typeExpr = .reject failure (s 2 [event nameA]) := rfl
  dsimp only [s] at marker guard noComma noClose report
  apply parseTupleType_reject_iff_list.mpr
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, guard, Bool.false_eq_true, if_false, child]
  change afterDelimitedElement typeExpr .rightParen true .typeExpr .typeExpr (sym 0 1 .leftParen)
    (4 + 1) [ty nameA] (s 2 [event nameA]) = _
  dsimp only [s]
  simp only [afterDelimitedElement, noComma, noClose, Bool.false_eq_true, if_false, report]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem canonical_lexing :
    Lexer.lex (file emptyText) = .ok (carrier emptyTokens) ∧
    Lexer.lex (file singleText) = .ok (carrier singleTokens) ∧
    Lexer.lex (file pairText) = .ok (carrier pairTokens) ∧
    Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  repeat' constructor
  all_goals apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  all_goals decide +kernel

theorem canonical_empty_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file emptyText) = .ok lexed ∧
      parseTupleType typeExpr { State.initial (file emptyText) lexed with diagnosticsRev := prior.reverse } =
        .ok { span := span 0 2, value := .tuple [] } output ∧
      output = state emptyText emptyTokens prior 2 [] ∧ output.diagnostics = prior ∧
      output.window = { endIndex := 3, endByte := 7 } ∧ output.peek? = some (tailToken 3) := by
  refine ⟨_, _, canonical_lexing.1, empty_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_reverse, List.reverse_nil, List.nil_append]

theorem canonical_singleton_trailing_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file singleText) = .ok lexed ∧
      parseTupleType typeExpr { State.initial (file singleText) lexed with diagnosticsRev := prior.reverse } =
        .ok { span := span 0 6, value := .tuple [ty nameA] } output ∧
      output = state singleText singleTokens prior 4 [event nameA] ∧ output.diagnostics = prior ++ [event nameA] ∧
      output.window = { endIndex := 5, endByte := 11 } ∧ output.peek? = some (tailToken 7) := by
  refine ⟨_, _, canonical_lexing.2.1, single_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem canonical_two_element_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file pairText) = .ok lexed ∧
      parseTupleType typeExpr { State.initial (file pairText) lexed with diagnosticsRev := prior.reverse } =
        .ok { span := span 0 10, value := .tuple [ty nameA, ty nameC] } output ∧
      output = state pairText pairTokens prior 6 [event nameA, event nameC] ∧
      output.diagnostics = prior ++ [event nameA, event nameC] ∧
      output.window = { endIndex := 7, endByte := 15 } ∧ output.peek? = some (tailToken 11) := by
  refine ⟨_, _, canonical_lexing.2.2.1, pair_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem canonical_missing_separator (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseTupleType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 2 [event nameA] ∧
      output.diagnostics = prior ++ [event nameA] ∧ output.window = { endIndex := 5, endByte := 12 } ∧
      output.peek? = some (sym 5 6 .plus) ∧ output.tokens[4]? = some (tailToken 8) ∧
      failure.expected.toList = [.symbol .comma, .symbol .rightParen] := by
  refine ⟨_, _, canonical_lexing.2.2.2, rejected_exec prior, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalTupleTypeTraceExamples
