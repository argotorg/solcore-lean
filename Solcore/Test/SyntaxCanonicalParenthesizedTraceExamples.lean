import Solcore.Syntax.Parser.ParenthesizedTraceCorrespondenceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties

/-! Canonical checked-name parentheses distinguish a singleton trailing-comma
group from a two-element tuple. Independent token derivations execute through
trace completeness; only canonical lexing uses kernel decision. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalParenthesizedTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

def source : SourceId := { origin := .main, path := "canonical-parenthesized-trace.sol" }
def file (content : String) : SourceFile := { id := source, content }
def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
def nameA : Identifier := { span := span 1 4, value := "a-b" }
def nameC : Identifier := { span := span 5 8, value := "c-d" }
def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
def nameExpr (name : Identifier) : Expr := { span := name.span, value := .identifier name }
def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
def initial (text : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file text) (carrier tokens) with diagnosticsRev := prior.reverse
}
def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}

theorem name_trace {input : Remainder} (name : Identifier) (endByte : Nat)
    (token : TokenAt input.tokens input.endIndex input.cursor (nameToken name))
    (spelling : IdentifierHyphenSpelling name.value) :
    IdentifierExpressionTraceParses source endByte input (nameExpr name)
      { input with cursor := input.cursor + 1 } [hyphen name] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := token.token_unique other <;> cases impossible
  exact .parsed (.identifier absent (.parsed ⟨token, rfl, rfl, rfl⟩ (.hyphen spelling)))

theorem peek_of_remainder {output : State} {after : Remainder} {token : Token}
    (same : output.declarativeRemainder = after)
    (current : TokenAt after.tokens after.endIndex after.cursor token) : output.peek? = some token := by
  have actual : TokenAt output.tokens output.window.endIndex output.cursor token := by
    simpa only [← same, State.declarativeRemainder] using current
  simp only [State.peek?, actual.1, if_true, actual.2]

private theorem success_exec (text : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (value : Expr) (after : Remainder) (events : List ParseDiagnostic)
    (parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses source
      (file text).content.utf8ByteSize (remainder tokens 0) value after events) :
    ∃ output, parenthesized identifierExpression (initial text tokens prior) = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ events ∧
      output.file = file text ∧ output.window = (initial text tokens prior).window := by
  rcases parenthesized_trace_success_complete identifierExpression_trace_success_complete
      identifierExpression_success_context (input := initial text tokens prior) parsed with
    ⟨output, result, afterEq, diagnostics⟩
  have frame := parenthesized_success_context identifierExpression_success_context result
  refine ⟨output, result, afterEq, ?_, frame.1, frame.2⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics

def groupText : String := "(a-b,) tail"
def groupTokens : List Token := [sym 0 1 .leftParen, nameToken nameA, sym 4 5 .comma,
  sym 5 6 .rightParen, { span := span 7 11, value := .identifier "tail" }]
def groupValue : Expr := { span := span 0 6, value := .group (nameExpr nameA) }

private theorem group_parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses source 11
    (remainder groupTokens 0) groupValue (remainder groupTokens 4) [hyphen nameA] :=
  .tuple (span 0 1) (span 5 6) (afterOpening := remainder groupTokens 1)
    (afterFirst := remainder groupTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, remainder, groupTokens, nameToken])
    (name_trace (input := remainder groupTokens 1) nameA 11 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.trailing (span 4 5) (span 5 6) (afterComma := remainder groupTokens 3)
      ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩)

def tupleText : String := "(a-b,c-d) tail"
def tupleTokens : List Token := [sym 0 1 .leftParen, nameToken nameA, sym 4 5 .comma,
  nameToken nameC, sym 8 9 .rightParen, { span := span 10 14, value := .identifier "tail" }]
def tupleValue : Expr := {
  span := span 0 9, value := .tuple { span := span 0 9, elements := [nameExpr nameA, nameExpr nameC] }
}

private theorem tuple_parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses source 14
    (remainder tupleTokens 0) tupleValue (remainder tupleTokens 5) [hyphen nameA, hyphen nameC] :=
  .tuple (span 0 1) (span 8 9) (afterOpening := remainder tupleTokens 1)
    (afterFirst := remainder tupleTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleTokens, nameToken])
    (name_trace (input := remainder tupleTokens 1) nameA 14 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.final (span 4 5) (span 8 9) (afterComma := remainder tupleTokens 3)
      (afterElement := remainder tupleTokens 4) ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleTokens, nameToken])
      (name_trace (input := remainder tupleTokens 3) nameC 14 ⟨by decide, rfl⟩
        (by unfold IdentifierHyphenSpelling nameC; decide)) (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleTokens, sym]) ⟨⟨by decide, rfl⟩, rfl⟩)

def emptyText : String := "() tail"
def emptyTokens : List Token := [sym 0 1 .leftParen, sym 1 2 .rightParen,
  { span := span 3 7, value := .identifier "tail" }]
def emptyValue : Expr := { span := span 0 2, value := .tuple { span := span 0 2, elements := [] } }

private theorem empty_parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses source 7
    (remainder emptyTokens 0) emptyValue (remainder emptyTokens 2) [] :=
  .empty (span 0 1) (span 1 2) (afterOpening := remainder emptyTokens 1)
    ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩

theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

set_option maxRecDepth 16384 in
theorem group_lexes : Lexer.lex (file groupText) = .ok (carrier groupTokens) := by
  apply lex_ok_of_toOption
  decide +kernel
set_option maxRecDepth 16384 in
theorem tuple_lexes : Lexer.lex (file tupleText) = .ok (carrier tupleTokens) := by
  apply lex_ok_of_toOption
  decide +kernel
set_option maxRecDepth 16384 in
theorem empty_lexes : Lexer.lex (file emptyText) = .ok (carrier emptyTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- A written trailing comma does not turn one element into a tuple: the
actual parser returns the complete group AST and exactly one name event. -/
theorem canonical_singleton_trailing_is_group (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file groupText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file groupText) lexed with diagnosticsRev := prior.reverse } = .ok groupValue output ∧
      output.declarativeRemainder = remainder groupTokens 4 ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.file = file groupText ∧ output.window = { endIndex := 5, endByte := 11 } ∧
      output.peek? = some { span := span 7 11, value := .identifier "tail" } := by
  rcases success_exec groupText groupTokens prior _ _ _ group_parsed with
    ⟨output, result, after, events, fileEq, window⟩
  exact ⟨carrier groupTokens, output, group_lexes, result, after, events, fileEq, window,
    peek_of_remainder after ⟨by decide, rfl⟩⟩

/-- Two written elements produce a tuple in source order, keeping the outer
and list spans, both checked-name events, the whole parent window, and `tail`. -/
theorem canonical_two_elements_is_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file tupleText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file tupleText) lexed with diagnosticsRev := prior.reverse } = .ok tupleValue output ∧
      output.declarativeRemainder = remainder tupleTokens 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.file = file tupleText ∧ output.window = { endIndex := 6, endByte := 14 } ∧
      output.peek? = some { span := span 10 14, value := .identifier "tail" } := by
  rcases success_exec tupleText tupleTokens prior _ _ _ tuple_parsed with
    ⟨output, result, after, events, fileEq, window⟩
  exact ⟨carrier tupleTokens, output, tuple_lexes, result, after, events, fileEq, window,
    peek_of_remainder after ⟨by decide, rfl⟩⟩

theorem canonical_empty_is_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file emptyText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file emptyText) lexed with diagnosticsRev := prior.reverse } = .ok emptyValue output ∧
      output.declarativeRemainder = remainder emptyTokens 2 ∧ output.diagnostics = prior ∧
      output.file = file emptyText ∧ output.window = { endIndex := 3, endByte := 7 } ∧
      output.peek? = some { span := span 3 7, value := .identifier "tail" } := by
  rcases success_exec emptyText emptyTokens prior _ _ _ empty_parsed with
    ⟨output, result, after, events, fileEq, window⟩
  exact ⟨carrier emptyTokens, output, empty_lexes, result, after, by simpa only [List.append_nil] using events,
    fileEq, window, peek_of_remainder after ⟨by decide, rfl⟩⟩

end Solcore.Test.SyntaxCanonicalParenthesizedTraceExamples
