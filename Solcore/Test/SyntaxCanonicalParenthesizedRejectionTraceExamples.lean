import Solcore.Test.SyntaxCanonicalParenthesizedTraceExamples
import Solcore.Syntax.Parser.ParenthesizedRejectionTraceCorrespondenceProperties
import Solcore.Syntax.Parser.Expression.AtomProperties

/-! Canonical closing failures after successful checked-name children. The
bespoke parenthesized parser expects only right parenthesis at these points,
not the generic delimiter pair. Earlier events survive; the report is uncommitted. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalParenthesizedRejectionTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Test.SyntaxCanonicalParenthesizedTraceExamples

def closingFailure (first last : Nat) : Failure := {
  span := span first last, found := some (.symbol .plus)
  expected := { head := .symbol .rightParen, tail := [] }, context := .expression
}

def groupRejectionText : String := "(a-b +) tail"
def groupRejectionTokens : List Token := [sym 0 1 .leftParen, nameToken nameA,
  sym 5 6 .plus, sym 6 7 .rightParen, { span := span 8 12, value := .identifier "tail" }]

private theorem group_rejected :
    ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 12
      (remainder groupRejectionTokens 0) (remainder groupRejectionTokens 2)
      (closingFailure 5 6).toDiagnostic [hyphen nameA] :=
  .closingMissing (span 0 1) (afterOpening := remainder groupRejectionTokens 1)
    (afterElement := remainder groupRejectionTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, remainder, groupRejectionTokens, nameToken])
    (name_trace (input := remainder groupRejectionTokens 1) nameA 12 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (by simp [TokenKindAbsentAt, TokenAt, remainder, groupRejectionTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, remainder, groupRejectionTokens, sym])
    (.reported (.token (current := sym 5 6 .plus) ⟨by decide, rfl⟩))

def tupleRejectionText : String := "(a-b,c-d +) tail"
def tupleRejectionTokens : List Token := [sym 0 1 .leftParen, nameToken nameA, sym 4 5 .comma,
  nameToken nameC, sym 9 10 .plus, sym 10 11 .rightParen,
  { span := span 12 16, value := .identifier "tail" }]

private theorem tuple_rejected :
    ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 16
      (remainder tupleRejectionTokens 0) (remainder tupleRejectionTokens 4)
      (closingFailure 9 10).toDiagnostic [hyphen nameA, hyphen nameC] := by
  have tail : ParenthesizedTupleTailTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source 16 (remainder tupleRejectionTokens 2) (remainder tupleRejectionTokens 4)
      (closingFailure 9 10).toDiagnostic [hyphen nameC] :=
    .closingMissing (span 4 5) (afterComma := remainder tupleRejectionTokens 3)
      (afterElement := remainder tupleRejectionTokens 4) ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleRejectionTokens, nameToken])
      (name_trace (input := remainder tupleRejectionTokens 3) nameC 16 ⟨by decide, rfl⟩
        (by unfold IdentifierHyphenSpelling nameC; decide)) (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleRejectionTokens, sym])
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleRejectionTokens, sym])
      (.reported (.token (current := sym 9 10 .plus) ⟨by decide, rfl⟩))
  exact .tailRejected (span 0 1) (span 4 5) (afterOpening := remainder tupleRejectionTokens 1)
    (afterFirst := remainder tupleRejectionTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleRejectionTokens, nameToken])
    (name_trace (input := remainder tupleRejectionTokens 1) nameA 16 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide) ⟨by decide, rfl⟩ tail

private theorem rejection_exec (text : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (failure : Failure) (after : Remainder) (events : List ParseDiagnostic)
    (rejected : ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source (file text).content.utf8ByteSize (remainder tokens 0) after failure.toDiagnostic events) :
    ∃ output, parenthesized identifierExpression (initial text tokens prior) = .reject failure output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ events ∧
      output.tokens = tokens.toArray ∧ output.window = (initial text tokens prior).window := by
  rcases (parenthesized_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context
      (input := initial text tokens prior)).mp rejected with ⟨output, result, afterEq, diagnostics⟩
  have frame := parenthesized_preservesTokenWindow identifierExpression
    identifierExpression_preservesTokenWindow (initial text tokens prior)
  rw [result] at frame
  refine ⟨output, result, afterEq, ?_, frame.1, frame.2⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics

set_option maxRecDepth 16384 in
theorem group_rejection_lexes : Lexer.lex (file groupRejectionText) = .ok (carrier groupRejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel
set_option maxRecDepth 16384 in
theorem tuple_rejection_lexes : Lexer.lex (file tupleRejectionText) = .ok (carrier tupleRejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- After the first successful child, only right parenthesis is expected.
Exactly one checked-name event follows every prior event; the plus remains current. -/
theorem canonical_group_closing_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file groupRejectionText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file groupRejectionText) lexed with diagnosticsRev := prior.reverse } =
        .reject (closingFailure 5 6) output ∧
      output.declarativeRemainder = remainder groupRejectionTokens 2 ∧
      output.diagnostics = prior ++ [hyphen nameA] ∧ output.window = { endIndex := 5, endByte := 12 } ∧
      output.peek? = some (sym 5 6 .plus) ∧
      output.tokens[4]? = some { span := span 8 12, value := .identifier "tail" } := by
  rcases rejection_exec groupRejectionText groupRejectionTokens prior _ _ _ group_rejected with
    ⟨output, result, after, events, tokens, window⟩
  refine ⟨carrier groupRejectionTokens, output, group_rejection_lexes, result, after, events, window,
    peek_of_remainder after ⟨by decide, rfl⟩, ?_⟩
  rw [tokens]
  rfl

/-- After a successful second child, the closing path still expects only
right parenthesis. Two ordered name events survive and the failure is not committed. -/
theorem canonical_tuple_closing_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file tupleRejectionText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file tupleRejectionText) lexed with diagnosticsRev := prior.reverse } =
        .reject (closingFailure 9 10) output ∧
      output.declarativeRemainder = remainder tupleRejectionTokens 4 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.window = { endIndex := 7, endByte := 16 } ∧ output.peek? = some (sym 9 10 .plus) ∧
      output.tokens[6]? = some { span := span 12 16, value := .identifier "tail" } := by
  rcases rejection_exec tupleRejectionText tupleRejectionTokens prior _ _ _ tuple_rejected with
    ⟨output, result, after, events, tokens, window⟩
  refine ⟨carrier tupleRejectionTokens, output, tuple_rejection_lexes, result, after, events, window,
    peek_of_remainder after ⟨by decide, rfl⟩, ?_⟩
  rw [tokens]
  rfl

end Solcore.Test.SyntaxCanonicalParenthesizedRejectionTraceExamples
