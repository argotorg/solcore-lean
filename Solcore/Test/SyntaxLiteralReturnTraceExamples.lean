import Solcore.Syntax.Parser.LiteralExpressionTraceProperties
import Solcore.Syntax.Parser.ReturnStatementSuccessTraceProperties
import Solcore.Syntax.Parser.ReturnStatementRejectionTraceCompletenessProperties

/-! Concrete empty and decimal returns through the actual literal-expression
leaf. General expression behavior is not asserted. Only canonical lexer
fixtures use kernel decision; parser outcomes follow independent trace rules. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLiteralReturnTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

def source : SourceId := { origin := .main, path := "literal-return-trace.sol" }
def file (content : String) : SourceFile := { id := source, content }
def byteSpan (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def marker (offset : Nat) : Token := { span := byteSpan offset (offset + 6), value := .keyword .returnKw }
def decimal (offset : Nat) : Token := { span := byteSpan offset (offset + 2), value := .decimalLiteral "42" }
def semicolon (offset : Nat) : Token := { span := byteSpan offset (offset + 1), value := .symbol .semicolon }
def literal42 (offset : Nat) : Expr := {
  span := byteSpan offset (offset + 2)
  value := .literal { span := byteSpan offset (offset + 2), value := .decimal "42" }
}
def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
def atCursor (tokens : List Token) (cursor : Nat) : Remainder := { tokens := tokens.toArray, endIndex := tokens.length, cursor }
def initial (content : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with diagnosticsRev := prior.reverse
}

/-- Located decimal-token recognition instantiates the actual literal grammar,
retaining the original spelling, expression span, and empty event sequence. -/
theorem literal42_trace {input : Remainder} (offset : Nat)
    (reportSource : SourceId) (endByte : Nat)
    (token : TokenAt input.tokens input.endIndex input.cursor (decimal offset)) :
    LiteralExpressionTraceParses reportSource endByte input (literal42 offset)
      { input with cursor := input.cursor + 1 } [] :=
  ⟨.parsed (.decimal token), rfl⟩

/-- The concrete `return;` skips every supplied expression parser, even one
that would reject, emit events, or return an invariant on this input. -/
theorem empty_return_bypasses_expression (expression : Parser Expr) (prior : List ParseDiagnostic) :
    returnStatement expression (initial "return;" [marker 0, semicolon 6] prior) =
      .ok { span := byteSpan 0 7, value := .returnStmt none }
        { initial "return;" [marker 0, semicolon 6] prior with cursor := 2 } :=
  returnStatement_eq_ok_none_of_exactTokens expression
    (input := initial "return;" [marker 0, semicolon 6] prior)
    (markerSpan := byteSpan 0 6) (semicolonSpan := byteSpan 6 7)
    (afterMarker := atCursor [marker 0, semicolon 6] 1)
    (after := atCursor [marker 0, semicolon 6] 2)
    ⟨⟨by change 0 < 2; decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩

def completeTokens : List Token := [marker 0, decimal 7, semicolon 9]
def returnedLiteral : Statement := { span := byteSpan 0 10, value := .returnStmt (some (literal42 7)) }

private theorem completeParsed : ReturnStatementTraceParses LiteralExpressionTraceParses
    source 10 (atCursor completeTokens 0) returnedLiteral (atCursor completeTokens 3) [] :=
  .parsed (byteSpan 0 6) (byteSpan 9 10)
    (afterMarker := atCursor completeTokens 1) (afterValue := atCursor completeTokens 2)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, atCursor, completeTokens, decimal])
      (literal42_trace 7 source 10 ⟨by decide, rfl⟩))
    ⟨⟨by decide, rfl⟩, rfl⟩

theorem literal_return_retains_prior (prior : List ParseDiagnostic) :
    ∃ output, returnStatement literalExpression (initial "return 42;" completeTokens prior) =
        .ok returnedLiteral output ∧ output.declarativeRemainder = atCursor completeTokens 3 ∧
      output.diagnostics = prior := by
  simpa only [initial, State.diagnostics, State.initial, List.reverse_reverse, List.append_nil] using
    (returnStatement_trace_success_iff literalExpression_trace_success_sound
      literalExpression_trace_success_complete (input := initial "return 42;" completeTokens prior)).mp completeParsed

def missingTokens : List Token := [marker 0, decimal 7]
def missingFailure : Failure := {
  span := byteSpan 9 9, found := none
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}

private theorem missingParsed : ReturnStatementTraceRejects LiteralExpressionTraceParses
    LiteralExpressionTraceRejects source 9 (atCursor missingTokens 0)
      (atCursor missingTokens 2) missingFailure.toDiagnostic [] :=
  .semicolonRejected (byteSpan 0 6)
    (afterMarker := atCursor missingTokens 1) (afterValue := atCursor missingTokens 2)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, atCursor, missingTokens, decimal])
      (literal42_trace 7 source 9 ⟨by decide, rfl⟩))
    (by simp [TokenKindAbsentAt, TokenAt, atCursor, missingTokens])
    (.reported (.windowEnd (by decide)))

/-- The literal has already been consumed when EOF reports the mandatory
semicolon at byte 9. The exact failure remains outside all prior events. -/
theorem literal_return_window_end_failure (prior : List ParseDiagnostic) :
    ∃ output, returnStatement literalExpression (initial "return 42" missingTokens prior) =
        .reject missingFailure output ∧ output.declarativeRemainder = atCursor missingTokens 2 ∧
      output.diagnostics = prior := by
  simpa only [initial, State.diagnostics, State.initial, List.reverse_reverse, List.append_nil] using
    (returnStatement_trace_reject_failure_iff literalExpression_trace_success_sound
      literalExpression_trace_reject_sound literalExpression_trace_success_complete
      literalExpression_trace_reject_complete literalExpression_success_context
      (input := initial "return 42" missingTokens prior)).mp missingParsed

private theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

set_option maxRecDepth 8192 in
theorem complete_lexes : Lexer.lex (file "return 42;") = .ok (carrier completeTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 8192 in
theorem missing_lexes : Lexer.lex (file "return 42") = .ok (carrier missingTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_literal_return (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file "return 42;") = .ok lexed ∧
      returnStatement literalExpression
          { State.initial (file "return 42;") lexed with diagnosticsRev := prior.reverse } =
        .ok returnedLiteral output ∧
      output.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 3, cursor := 3 } ∧
      output.diagnostics = prior := by
  rcases literal_return_retains_prior prior with ⟨output, result⟩
  exact ⟨carrier completeTokens, output, complete_lexes, result⟩

theorem canonical_literal_return_missing_semicolon (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file "return 42") = .ok lexed ∧
      returnStatement literalExpression
          { State.initial (file "return 42") lexed with diagnosticsRev := prior.reverse } =
        .reject missingFailure output ∧
      output.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 2, cursor := 2 } ∧
      output.diagnostics = prior := by
  rcases literal_return_window_end_failure prior with ⟨output, result⟩
  exact ⟨carrier missingTokens, output, missing_lexes, result⟩

end Solcore.Test.SyntaxLiteralReturnTraceExamples
