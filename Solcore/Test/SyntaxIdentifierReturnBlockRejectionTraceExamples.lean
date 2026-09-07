import Solcore.Test.SyntaxIdentifierReturnBlockTraceExamples

/-! An actual checked identifier expression succeeds before its return's
mandatory semicolon rejects. Canonical lexing and independent trace derivations
keep the name event separate from the final report and isolation commit. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxIdentifierReturnBlockRejectionTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxIdentifierReturnBlockTraceExamples

def rejectionText : String := "{ return a-b + } tail"
def rejectionTokens : List Token := [
  { span := span 0 1, value := .symbol .leftBrace }, marker 2, nameToken nameA,
  { span := span 13 14, value := .symbol .plus },
  { span := span 15 16, value := .symbol .rightBrace },
  { span := span 17 21, value := .identifier "tail" }]
def rejectionRem (endIndex cursor : Nat) : Remainder := { tokens := rejectionTokens.toArray, endIndex, cursor }
def rejectionState (prior : List ParseDiagnostic) : State := initial rejectionText rejectionTokens prior
def semicolonFailure : Failure := {
  span := span 13 14, found := some (.symbol .plus)
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}

private theorem rejectionParsed (policy : CoreBlockTailPolicy)
    (reportSource : SourceId) (endByte endIndex : Nat) (inside : 3 < endIndex) :
    CoreBlockTraceRejects (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      (ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects) policy
      reportSource endByte (rejectionRem endIndex 0) (rejectionRem endIndex 3)
      semicolonFailure.toDiagnostic [hyphen nameA] := by
  have rejected : ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      reportSource endByte (rejectionRem endIndex 1) (rejectionRem endIndex 3)
      semicolonFailure.toDiagnostic [hyphen nameA] :=
    .semicolonRejected (span 2 8)
      (afterMarker := rejectionRem endIndex 2) (afterValue := rejectionRem endIndex 3)
      ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
      (.present (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens, nameToken])
        (name_trace nameA reportSource endByte ⟨by change 2 < endIndex; omega, rfl⟩ (by
          unfold IdentifierHyphenSpelling nameA; decide)))
      (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens])
      (.reported (.token (current := { span := span 13 14, value := .symbol .plus }) ⟨inside, rfl⟩))
  exact .itemsRejected (span 0 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩
    (.statementRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens, marker]) rejected)

private def capture : BalancedBlockCapture := { span := span 0 16, endIndex := 5, endByte := 16 }

private theorem rejectionCaptured : BalancedBlockCaptures (rejectionRem 6 0) capture :=
  .captured (input := rejectionRem 6 0) (openingSpan := span 0 1) (closingSpan := span 15 16)
    ⟨by decide, rfl⟩
    (.other (token := marker 2) ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := nameToken nameA) ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := { span := span 13 14, value := .symbol .plus })
          ⟨by decide, rfl⟩ (by decide) (by decide) (.close ⟨by decide, rfl⟩))))

/-- The exact semicolon failure is still uncommitted. Only the successful
name's event follows prior events; neither tail validation nor recovery ran. -/
theorem name_return_rejection_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (returnStatement identifierExpression) policy (rejectionState prior) =
        .reject semicolonFailure output ∧ output.declarativeRemainder = rejectionRem 6 3 ∧
      output.diagnostics = prior ++ [hyphen nameA] := by
  simpa only [rejectionState, initial, State.initial, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_reject_failure_iff
      (returnStatement_trace_success_sound identifierExpression_trace_success_sound)
      (returnStatement_reject_trace_sound identifierExpression_trace_success_sound
        identifierExpression_trace_reject_sound identifierExpression_success_context)
      (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
      (returnStatement_trace_reject_complete identifierExpression_trace_success_complete
        identifierExpression_trace_reject_complete identifierExpression_success_context)
      (returnStatement_success_context identifierExpression_success_context) policy
      (input := rejectionState prior)).mp (rejectionParsed policy.declarative source 21 6 (by decide))

/-- One isolation commits exactly one report after the name event and returns
the captured empty block. The child byte boundary is 16, parent 21; `tail` remains
unread with the complete parent file/window restored. -/
theorem name_return_rejection_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock (returnStatement identifierExpression) policy) (rejectionState prior) =
        .ok { span := span 0 16, value := [] } output ∧
      output.declarativeRemainder = rejectionRem 6 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, semicolonFailure.toDiagnostic] ∧
      output.file = (rejectionState prior).file ∧ output.window = (rejectionState prior).window ∧
      output.peek? = some { span := span 17 21, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses
      (CoreBlockTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses IdentifierExpressionTraceParses)
        (ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects) policy.declarative)
      source 21 (rejectionRem 6 0) { span := span 0 16, value := [] } (rejectionRem 6 5)
      [hyphen nameA, semicolonFailure.toDiagnostic] :=
    .recovered rejectionCaptured (rejectionParsed policy.declarative source 16 5 (by decide))
  rcases isolateBlock_success_trace_complete
      (coreBlock_trace_success_complete (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
        (returnStatement_success_context identifierExpression_success_context) policy)
      (coreBlock_trace_reject_complete (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
        (returnStatement_trace_reject_complete identifierExpression_trace_success_complete
          identifierExpression_trace_reject_complete identifierExpression_success_context)
        (returnStatement_success_context identifierExpression_success_context) policy)
      (input := rejectionState prior) parsed with ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := rejectionState prior) rejectionCaptured with
    ⟨captured, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [rejectionState, initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens.toArray at tokens
    change output.window.endIndex = 6 at endpoint
    change output.cursor = 5 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

set_option maxRecDepth 16384 in
theorem rejection_lexes : Lexer.lex (file rejectionText) = .ok (carrier rejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

end Solcore.Test.SyntaxIdentifierReturnBlockRejectionTraceExamples
