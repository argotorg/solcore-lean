import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples
import Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceCorrespondenceProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! After a comma, a non-closing token invokes the checked-name child. Without
a comma, the same token reports the ordered delimiter pair instead. Both paths
retain earlier name events without committing their final rejection report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalDelimitedTrailingRejectionTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

private def childText : String := "<a-b,+> tail"
private def childTokens : List Token := [sym 0 1 .less, nameToken nameA, sym 4 5 .comma,
  sym 5 6 .plus, sym 6 7 .greater, { span := span 8 12, value := .identifier "tail" }]
private def childFailure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}
private def delimiterText : String := "<a-b +> tail"
private def delimiterTokens : List Token := [sym 0 1 .less, nameToken nameA,
  sym 5 6 .plus, sym 6 7 .greater, { span := span 8 12, value := .identifier "tail" }]
private def delimiterFailure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .greater] }, context := .expression
}

private theorem child_rejected : TrailingDelimitedListTraceRejects .less .greater false .expression
    IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 12
      (remainder childTokens 0) (remainder childTokens 3) childFailure.toDiagnostic [hyphen nameA] := by
  have child : IdentifierExpressionTraceRejects source 12 (remainder childTokens 3)
      (remainder childTokens 3) childFailure.toDiagnostic [] :=
    ⟨by constructor <;> simp [TokenKindAbsentAt, TokenAt, remainder, childTokens, sym],
      .absent (by simp [IdentifierAbsentAt, TokenAt, remainder, childTokens, sym]),
      .reported (.token (current := sym 5 6 .plus) ⟨by decide, rfl⟩), rfl⟩
  exact .tailRejected (span 0 1) (afterOpening := remainder childTokens 1)
    (afterFirst := remainder childTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩ .disabled
    (name_trace (input := remainder childTokens 1) nameA 12 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.elementRejected (span 4 5) ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, childTokens, sym]) child)

private theorem delimiter_rejected : TrailingDelimitedListTraceRejects .less .greater false .expression
    IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 12
      (remainder delimiterTokens 0) (remainder delimiterTokens 2) delimiterFailure.toDiagnostic [hyphen nameA] :=
  .tailRejected (span 0 1) (afterOpening := remainder delimiterTokens 1)
    (afterFirst := remainder delimiterTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩ .disabled
    (name_trace (input := remainder delimiterTokens 1) nameA 12 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.delimiterMissing
      (by simp [TokenKindAbsentAt, TokenAt, remainder, delimiterTokens, sym])
      (by simp [TokenKindAbsentAt, TokenAt, remainder, delimiterTokens, sym])
      (.reported (.token (current := sym 5 6 .plus) ⟨by decide, rfl⟩)))

private theorem rejection_exec (content : String) (inputTokens : List Token) (prior : List ParseDiagnostic)
    (failure : Failure) (after : Remainder)
    (rejection : TrailingDelimitedListTraceRejects .less .greater false .expression
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source (file content).content.utf8ByteSize
      (remainder inputTokens 0) after failure.toDiagnostic [hyphen nameA]) :
    ∃ output, delimited .less .greater false identifierExpression .expression .expression
        (initial content inputTokens prior) = .reject failure output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.tokens = inputTokens.toArray ∧ output.window = (initial content inputTokens prior).window := by
  rcases (delimited_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context
      .less .greater false .expression .expression (input := initial content inputTokens prior)).mp rejection with
    ⟨output, result, afterEq, diagnostics⟩
  have frame := delimited_preservesTokenWindow .less .greater false identifierExpression .expression .expression
    identifierExpression_preservesTokenWindow (initial content inputTokens prior)
  rw [result] at frame
  refine ⟨output, result, afterEq, ?_, frame.1, frame.2⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics

set_option maxRecDepth 16384 in
theorem rejected_child_lexes : Lexer.lex (file childText) = .ok (carrier childTokens) := by
  apply lex_ok_of_toOption
  decide +kernel
set_option maxRecDepth 16384 in
theorem missing_delimiter_lexes : Lexer.lex (file delimiterText) = .ok (carrier delimiterTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_child_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file childText) = .ok lexed ∧
      delimited .less .greater false identifierExpression .expression .expression
        { State.initial (file childText) lexed with diagnosticsRev := prior.reverse } = .reject childFailure output ∧
      output.declarativeRemainder = remainder childTokens 3 ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.window = { endIndex := 6, endByte := 12 } ∧ output.peek? = some (sym 5 6 .plus) ∧
      output.tokens[5]? = some { span := span 8 12, value := .identifier "tail" } := by
  rcases rejection_exec childText childTokens prior _ _ child_rejected with
    ⟨output, result, after, events, tokenEq, window⟩
  refine ⟨carrier childTokens, output, rejected_child_lexes, result, after, events, window,
    peek_of_remainder after ⟨by decide, rfl⟩, ?_⟩
  rw [tokenEq]
  rfl

theorem canonical_delimiter_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file delimiterText) = .ok lexed ∧
      delimited .less .greater false identifierExpression .expression .expression
        { State.initial (file delimiterText) lexed with diagnosticsRev := prior.reverse } = .reject delimiterFailure output ∧
      output.declarativeRemainder = remainder delimiterTokens 2 ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.window = { endIndex := 5, endByte := 12 } ∧ output.peek? = some (sym 5 6 .plus) ∧
      output.tokens[4]? = some { span := span 8 12, value := .identifier "tail" } := by
  rcases rejection_exec delimiterText delimiterTokens prior _ _ delimiter_rejected with
    ⟨output, result, after, events, tokenEq, window⟩
  refine ⟨carrier delimiterTokens, output, missing_delimiter_lexes, result, after, events, window,
    peek_of_remainder after ⟨by decide, rfl⟩, ?_⟩
  rw [tokenEq]
  rfl

end Solcore.Test.SyntaxCanonicalDelimitedTrailingRejectionTraceExamples
