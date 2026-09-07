import Solcore.Test.SyntaxDotConstructorSuccessTraceProperties
import Solcore.Test.SyntaxDotConstructorRejectionTraceProperties
import Solcore.Syntax.Parser.Expression.AtomProperties

/-! Canonical source-to-dot-constructor traces reuse the independently proved
consumer outcomes. The rejection carrier matches its existing explicit fixture.
Only lexer equations use kernel decision; parser outcomes use trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalDotConstructorTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "dot-rejection-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def nameA : Identifier := { span := span 1 4, value := "a-b" }
private def nameC : Identifier := { span := span 5 8, value := "c-d" }
private def nameE : Identifier := { span := span 9 12, value := "e-f" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def nameExpr (name : Identifier) : Expr := { span := name.span, value := .identifier name }
private def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def initial (text : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file text) (carrier tokens) with diagnosticsRev := prior.reverse
}
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}

private def successText : String := ".a-b(c-d,e-f) tail"
private def successTokens : List Token := [sym 0 1 .dot, nameToken nameA, sym 4 5 .leftParen,
  nameToken nameC, sym 8 9 .comma, nameToken nameE, sym 12 13 .rightParen,
  { span := span 14 18, value := .identifier "tail" }]
private def successValue : Expr := {
  span := span 0 13
  value := .dotConstructor (span 0 1) nameA
    (some { span := span 4 13, elements := [nameExpr nameC, nameExpr nameE] })
}

private theorem success_from_tokens (prior : List ParseDiagnostic) :
    ∃ output, dotConstructor identifierExpression (initial successText successTokens prior) =
        .ok successValue output ∧ output.declarativeRemainder = remainder successTokens 7 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC, hyphen nameE] := by
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse,
    successValue, nameExpr, hyphen, SourceSpan.cover, span] using
    SyntaxDotConstructorSuccessTraceProperties.checked_constructor_and_arguments_keep_event_order
      (input := initial successText successTokens prior)
      (dotSpan := span 0 1) (openingSpan := span 4 5) (commaSpan := span 8 9) (closingSpan := span 12 13)
      (name := nameA) (first := nameC) (second := nameE)
      (afterDot := remainder successTokens 1) (afterName := remainder successTokens 2)
      (afterOpening := remainder successTokens 3) (afterFirst := remainder successTokens 4)
      (afterComma := remainder successTokens 5) (afterSecond := remainder successTokens 6)
      (after := remainder successTokens 7)
      ⟨⟨by change 0 < 8; decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)
      ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩
      (by unfold IdentifierHyphenSpelling nameC; decide)
      ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩
      (by unfold IdentifierHyphenSpelling nameE; decide) ⟨⟨by decide, rfl⟩, rfl⟩

private def rejectionText : String := ".a-b(c-d,+) tail"
private def rejectionTokens : List Token := [sym 0 1 .dot, nameToken nameA, sym 4 5 .leftParen,
  nameToken nameC, sym 8 9 .comma, sym 9 10 .plus, sym 10 11 .rightParen,
  { span := span 12 16, value := .identifier "tail" }]
private def plusFailure : Failure := {
  span := span 9 10, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem rejection_from_tokens (prior : List ParseDiagnostic) :
    ∃ output, dotConstructor identifierExpression (initial rejectionText rejectionTokens prior) =
        .reject plusFailure output ∧ output.declarativeRemainder = remainder rejectionTokens 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] :=
  SyntaxDotConstructorRejectionTraceProperties.name_and_argument_events_precede_uncommitted_failure prior

private theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

set_option maxRecDepth 16384 in
theorem success_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 16384 in
theorem rejection_lexes : Lexer.lex (file rejectionText) = .ok (carrier rejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Canonical lexing connects directly to the actual parser's root state.
The outer expression, dot, name, and argument-list spans are all retained;
constructor-name and two argument-name events follow arbitrary prior events. -/
theorem canonical_dot_constructor_success (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      dotConstructor identifierExpression
        { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } = .ok successValue output ∧
      output.declarativeRemainder = remainder successTokens 7 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC, hyphen nameE] ∧
      output.file = file successText ∧ output.window = { endIndex := 8, endByte := 18 } ∧
      output.peek? = some { span := span 14 18, value := .identifier "tail" } := by
  rcases success_from_tokens prior with ⟨output, result, after, events⟩
  have frame := dotConstructor_success_context identifierExpression_success_context result
  refine ⟨carrier successTokens, output, success_lexes, result, after, events, frame.1, frame.2, ?_⟩
  have tokens := congrArg Remainder.tokens after
  have endpoint := congrArg Remainder.endIndex after
  have cursor := congrArg Remainder.cursor after
  change output.tokens = successTokens.toArray at tokens
  change output.window.endIndex = 8 at endpoint
  change output.cursor = 7 at cursor
  simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
  rfl

/-- The comma invokes the actual checked-name child and its full identifier
failure escapes unchanged. Only the constructor and first argument events are
committed; the plus, closing parenthesis, and later tail remain unconsumed. -/
theorem canonical_dot_constructor_rejection (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectionText) = .ok lexed ∧
      dotConstructor identifierExpression
        { State.initial (file rejectionText) lexed with diagnosticsRev := prior.reverse } =
        .reject plusFailure output ∧ output.declarativeRemainder = remainder rejectionTokens 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.window = { endIndex := 8, endByte := 16 } ∧ output.peek? = some (sym 9 10 .plus) ∧
      output.tokens[7]? = some { span := span 12 16, value := .identifier "tail" } := by
  rcases rejection_from_tokens prior with ⟨output, result, after, events⟩
  have frame := dotConstructor_preservesTokenWindow identifierExpression
    identifierExpression_preservesTokenWindow (initial rejectionText rejectionTokens prior)
  rw [result] at frame
  refine ⟨carrier rejectionTokens, output, rejection_lexes, result, after, events, frame.2, ?_, ?_⟩
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens.toArray at tokens
    change output.window.endIndex = 8 at endpoint
    change output.cursor = 5 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl
  · rw [frame.1]
    rfl

end Solcore.Test.SyntaxCanonicalDotConstructorTraceExamples
