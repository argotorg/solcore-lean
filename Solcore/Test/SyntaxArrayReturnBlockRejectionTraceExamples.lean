import Solcore.Test.SyntaxArrayReturnBlockTraceExamples

/-! A checked name event precedes an identifier-child failure in the array.
The return and raw block preserve that full report without committing it.
Only the single outer isolation recovers, restoring the exact parent tail. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxArrayReturnBlockRejectionTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxArrayReturnBlockTraceExamples

def rejectionText : String := "{ return [a-b,+]; } tail"
def rejectionTokens : List Token := [sym 0 1 .leftBrace, marker, sym 9 10 .leftBracket,
  nameToken nameA, sym 13 14 .comma, sym 14 15 .plus, sym 15 16 .rightBracket,
  sym 16 17 .semicolon, sym 18 19 .rightBrace,
  { span := span 20 24, value := .identifier "tail" }]
def childFailure : Failure := {
  span := span 14 15, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem array_rejected (endByte endIndex : Nat) (inside : 8 < endIndex) :
    arrayRejects source endByte (remainder rejectionTokens endIndex 2)
      (remainder rejectionTokens endIndex 5) childFailure.toDiagnostic [hyphen nameA] := by
  have child : IdentifierExpressionTraceRejects source endByte (remainder rejectionTokens endIndex 5)
      (remainder rejectionTokens endIndex 5) childFailure.toDiagnostic [] :=
    ⟨by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, remainder, rejectionTokens, sym],
      .absent (by simp [IdentifierAbsentAt, TokenAt, remainder, rejectionTokens, sym]),
      .reported (.token (current := sym 14 15 .plus) ⟨by change 5 < endIndex; omega, rfl⟩), rfl⟩
  unfold arrayRejects ArrayLiteralTraceRejects
  exact .tailRejected (span 9 10) (input := remainder rejectionTokens endIndex 2)
    (opening := .leftBracket) (closing := .rightBracket)
    (afterOpening := remainder rejectionTokens endIndex 3) (afterFirst := remainder rejectionTokens endIndex 4)
    ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩
    (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, rejectionTokens, nameToken]))
    (name_trace (input := remainder rejectionTokens endIndex 3) nameA endByte
      ⟨by change 3 < endIndex; omega, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
    (by change 3 < 4; decide)
    (.elementRejected (span 13 14) (afterComma := remainder rejectionTokens endIndex 5)
      ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩ child)

private theorem return_rejected (endByte endIndex : Nat) (inside : 8 < endIndex) :
    returnedRejects source endByte (remainder rejectionTokens endIndex 1)
      (remainder rejectionTokens endIndex 5) childFailure.toDiagnostic [hyphen nameA] :=
  .valueRejected (span 2 8) (afterMarker := remainder rejectionTokens endIndex 2)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    (.expressionRejected (by simp [TokenKindAbsentAt, TokenAt, remainder, rejectionTokens, sym])
      (array_rejected endByte endIndex inside))

private theorem block_rejected (policy : CoreBlockTailPolicy) (endByte endIndex : Nat)
    (inside : 8 < endIndex) :
    CoreBlockTraceRejects returnedTrace returnedRejects policy source endByte
      (remainder rejectionTokens endIndex 0) (remainder rejectionTokens endIndex 5)
      childFailure.toDiagnostic [hyphen nameA] :=
  .itemsRejected (span 0 1) (afterOpening := remainder rejectionTokens endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩
    (.statementRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, rejectionTokens, marker])
      (return_rejected endByte endIndex inside))

private def capture : BalancedBlockCapture := { span := span 0 19, endIndex := 9, endByte := 19 }
private theorem captured : BalancedBlockCaptures (remainder rejectionTokens 10 0) capture :=
  .captured (input := remainder rejectionTokens 10 0) (openingSpan := span 0 1) (closingSpan := span 18 19)
    ⟨by decide, rfl⟩
    (.other (token := marker) ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := sym 9 10 .leftBracket) ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := nameToken nameA) ⟨by decide, rfl⟩ (by decide) (by decide)
          (.other (token := sym 13 14 .comma) ⟨by decide, rfl⟩ (by decide) (by decide)
            (.other (token := sym 14 15 .plus) ⟨by decide, rfl⟩ (by decide) (by decide)
              (.other (token := sym 15 16 .rightBracket) ⟨by decide, rfl⟩ (by decide) (by decide)
                (.other (token := sym 16 17 .semicolon) ⟨by decide, rfl⟩ (by decide) (by decide)
                  (.close ⟨by decide, rfl⟩))))))))

/-- The array child's complete identifier report escapes return and raw block
unchanged. The following semicolon/brace are not reached and no report is committed. -/
theorem array_return_raw_rejection (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock arrayReturn policy (initial rejectionText rejectionTokens prior) =
        .reject childFailure output ∧ output.declarativeRemainder = remainder rejectionTokens 10 5 ∧
      output.diagnostics = prior ++ [hyphen nameA] ∧ output.peek? = some (sym 14 15 .plus) := by
  rcases (coreBlock_trace_reject_failure_iff arrayReturn_success_sound arrayReturn_reject_sound
      arrayReturn_success_complete arrayReturn_reject_complete arrayReturn_success_context policy
      (input := initial rejectionText rejectionTokens prior)).mp
      (block_rejected policy.declarative 24 10 (by decide)) with ⟨output, result, after, events⟩
  refine ⟨output, result, after, ?_, ?_⟩
  · simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens.toArray at tokens
    change output.window.endIndex = 10 at endpoint
    change output.cursor = 5 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

/-- One isolation discards the rejected body and appends the one child report
after the name event. Parent byte boundary 24 replaces child 19; `tail` is unread. -/
theorem array_return_isolated_recovery (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock arrayReturn policy) (initial rejectionText rejectionTokens prior) =
        .ok { span := span 0 19, value := [] } output ∧
      output.declarativeRemainder = remainder rejectionTokens 10 9 ∧
      output.diagnostics = prior ++ [hyphen nameA, childFailure.toDiagnostic] ∧
      output.file = file rejectionText ∧ output.window = { endIndex := 10, endByte := 24 } ∧
      output.peek? = some { span := span 20 24, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses (CoreBlockTraceParses returnedTrace policy.declarative)
      (CoreBlockTraceRejects returnedTrace returnedRejects policy.declarative) source 24
      (remainder rejectionTokens 10 0) { span := span 0 19, value := [] }
      (remainder rejectionTokens 10 9) [hyphen nameA, childFailure.toDiagnostic] :=
    .recovered captured (block_rejected policy.declarative 19 9 (by decide))
  rcases (isolatedCoreBlock_trace_success_iff arrayReturn_success_sound arrayReturn_reject_sound
      arrayReturn_success_complete arrayReturn_reject_complete arrayReturn_success_context policy
      (input := initial rejectionText rejectionTokens prior)).mp parsed with ⟨output, result, after, events⟩
  rcases BlockInternals.captureBlock?_complete (input := initial rejectionText rejectionTokens prior) captured with
    ⟨runtimeCapture, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens.toArray at tokens
    change output.window.endIndex = 10 at endpoint
    change output.cursor = 9 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

set_option maxRecDepth 16384 in
theorem rejection_lexes : Lexer.lex (file rejectionText) = .ok (carrier rejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_array_return_rejection (policy : TailExpressionPolicy) :
    ∃ lexed output, Lexer.lex (file rejectionText) = .ok lexed ∧
      coreBlock (returnStatement (arrayLiteral identifierExpression)) policy
        (State.initial (file rejectionText) lexed) = .reject childFailure output ∧
      output.declarativeRemainder = remainder rejectionTokens 10 5 ∧ output.diagnostics = [hyphen nameA] := by
  rcases array_return_raw_rejection policy [] with ⟨output, result, after, events, _⟩
  exact ⟨carrier rejectionTokens, output, rejection_lexes, result, after, events⟩

theorem canonical_array_return_recovery (policy : TailExpressionPolicy) :
    ∃ lexed output, Lexer.lex (file rejectionText) = .ok lexed ∧
      isolateBlock (coreBlock (returnStatement (arrayLiteral identifierExpression)) policy)
        (State.initial (file rejectionText) lexed) = .ok { span := span 0 19, value := [] } output ∧
      output.declarativeRemainder = remainder rejectionTokens 10 9 ∧
      output.diagnostics = [hyphen nameA, childFailure.toDiagnostic] ∧
      output.window = { endIndex := 10, endByte := 24 } ∧
      output.peek? = some { span := span 20 24, value := .identifier "tail" } := by
  rcases array_return_isolated_recovery policy [] with ⟨output, result, after, events, _, window, next⟩
  exact ⟨carrier rejectionTokens, output, rejection_lexes, result, after, events, window, next⟩

end Solcore.Test.SyntaxArrayReturnBlockRejectionTraceExamples
