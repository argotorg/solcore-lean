import Solcore.Syntax.Parser.ControlLeafDiagnosticTraceProperties
import Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties

/-! Actual control-leaf rejection inside a block. The explicit carrier for
`{ break; break + } tail` distinguishes the first keyword failure from the later
semicolon failure, and tests recovered parent continuation with prior events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxControlLeafBlockRejectionExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "control-block-reject.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def tokens : Array Token := #[
  { span := span 0 1, value := .symbol .leftBrace },
  { span := span 2 7, value := .keyword .breakKw },
  { span := span 7 8, value := .symbol .semicolon },
  { span := span 9 14, value := .keyword .breakKw },
  { span := span 15 16, value := .symbol .plus },
  { span := span 17 18, value := .symbol .rightBrace },
  { span := span 19 23, value := .identifier "tail" }]
private def remainder (endIndex cursor : Nat) : Remainder := { tokens, endIndex, cursor }
private def inputState (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "{ break; break + } tail" }
  tokens, cursor := 0, window := { endIndex := 7, endByte := 23 }
  diagnosticsRev := prior.reverse
}
private def semicolonFailure : Failure := {
  span := span 15 16, found := some (.symbol .plus)
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}
private def keywordFailure : Failure := {
  span := span 2 7, found := some (.keyword .breakKw)
  expected := { head := .keyword .continueKw, tail := [] }, context := .statement
}
private def capture : BalancedBlockCapture := { span := span 0 18, endIndex := 6, endByte := 18 }

private theorem firstBreak (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 5 < endIndex) :
    BreakStatementTraceParses reportSource endByte (remainder endIndex 1)
      { span := span 2 8, value := .breakStmt } (remainder endIndex 3) [] :=
  ⟨.parsed (span 2 7) (span 7 8) (afterMarker := remainder endIndex 2)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩

private theorem breakRejected (policy : CoreBlockTailPolicy)
    (reportSource : SourceId) (endByte endIndex : Nat) (inside : 5 < endIndex) :
    CoreBlockTraceRejects BreakStatementTraceParses BreakStatementTraceRejects policy
      reportSource endByte (remainder endIndex 0) (remainder endIndex 4)
      semicolonFailure.toDiagnostic [] := by
  have last : BreakStatementTraceRejects reportSource endByte (remainder endIndex 3)
      (remainder endIndex 4) semicolonFailure.toDiagnostic [] :=
    .semicolonMissing (span 9 14) ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens])
      (.reported (.token (current := { span := span 15 16, value := .symbol .plus })
        ⟨by change 4 < endIndex; omega, rfl⟩))
  have lastItem : CoreBlockItemsTraceRejects BreakStatementTraceParses BreakStatementTraceRejects
      reportSource endByte (remainder endIndex 3) (remainder endIndex 4)
      semicolonFailure.toDiagnostic [] :=
    .statementRejected (by change 3 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens]) last
  have items : CoreBlockItemsTraceRejects BreakStatementTraceParses BreakStatementTraceRejects
      reportSource endByte (remainder endIndex 1) (remainder endIndex 4)
      semicolonFailure.toDiagnostic [] :=
    .laterRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens])
      (firstBreak reportSource endByte endIndex inside) (by change 1 < 3; decide) lastItem
  exact .itemsRejected (span 0 1) (afterOpening := remainder endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items

private theorem continueRejected (policy : CoreBlockTailPolicy)
    (reportSource : SourceId) (endByte : Nat) :
    CoreBlockTraceRejects ContinueStatementTraceParses ContinueStatementTraceRejects policy
      reportSource endByte (remainder 7 0) (remainder 7 1) keywordFailure.toDiagnostic [] := by
  have leaf : ContinueStatementTraceRejects reportSource endByte
      (remainder 7 1) (remainder 7 1) keywordFailure.toDiagnostic [] :=
    .markerMissing (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens])
      (.reported (.token (current := { span := span 2 7, value := .keyword .breakKw })
        ⟨by decide, rfl⟩))
  exact .itemsRejected (span 0 1) (afterOpening := remainder 7 1)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (.statementRejected (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens]) leaf)

private theorem balancedCapture : BalancedBlockCaptures (remainder 7 0) capture :=
  .captured (input := remainder 7 0) (openingSpan := span 0 1) (closingSpan := span 17 18)
    ⟨by decide, rfl⟩
    (.other (token := { span := span 2 7, value := .keyword .breakKw })
      ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := { span := span 7 8, value := .symbol .semicolon })
        ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := { span := span 9 14, value := .keyword .breakKw })
          ⟨by decide, rfl⟩ (by decide) (by decide)
          (.other (token := { span := span 15 16, value := .symbol .plus })
            ⟨by decide, rfl⟩ (by decide) (by decide) (.close ⟨by decide, rfl⟩)))))

/-- The real break leaf consumes the first complete statement and the next
keyword, then returns the exact semicolon failure without committing it. -/
theorem break_later_semicolon_failure (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock breakStatement policy (inputState prior) = .reject semicolonFailure output ∧
      output.declarativeRemainder = remainder 7 4 ∧ output.diagnostics = prior := by
  simpa only [inputState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_reject_failure_iff breakStatement_trace_success_sound breakStatement_trace_reject_sound
      breakStatement_trace_success_complete breakStatement_trace_reject_complete breakStatement_success_context
      policy (input := inputState prior)).mp (breakRejected policy.declarative _ _ 7 (by decide))

/-- With the real continue leaf, the same input fails at the first break
keyword, before reaching either semicolon position or the later plus token. -/
theorem continue_keyword_failure_has_priority (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock continueStatement policy (inputState prior) = .reject keywordFailure output ∧
      output.declarativeRemainder = remainder 7 1 ∧ output.diagnostics = prior := by
  simpa only [inputState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_reject_failure_iff continueStatement_trace_success_sound continueStatement_trace_reject_sound
      continueStatement_trace_success_complete continueStatement_trace_reject_complete continueStatement_success_context
      policy (input := inputState prior)).mp (continueRejected policy.declarative _ _)

/-- Balanced recovery drops the unfinished body, commits only the semicolon
report once, and restores the byte-23 parent window after the byte-18 child.
All earlier events survive and the following `tail` token remains unread. -/
theorem break_captured_failure_restores_parent
    (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock breakStatement policy) (inputState prior) =
        .ok { span := span 0 18, value := [] } output ∧
      output.declarativeRemainder = remainder 7 6 ∧
      output.diagnostics = prior ++ [semicolonFailure.toDiagnostic] ∧
      output.file = (inputState prior).file ∧ output.window = (inputState prior).window ∧
      output.peek? = some { span := span 19 23, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses (CoreBlockTraceParses BreakStatementTraceParses policy.declarative)
      (CoreBlockTraceRejects BreakStatementTraceParses BreakStatementTraceRejects policy.declarative)
      source 23 (remainder 7 0) { span := span 0 18, value := [] }
      (remainder 7 6) [semicolonFailure.toDiagnostic] :=
    .recovered balancedCapture (breakRejected policy.declarative source 18 6 (by decide))
  rcases (isolatedCoreBlock_trace_success_iff (statement := breakStatement)
      breakStatement_trace_success_sound breakStatement_trace_reject_sound
      breakStatement_trace_success_complete breakStatement_trace_reject_complete
      breakStatement_success_context policy (input := inputState prior)).mp parsed with
    ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := inputState prior) balancedCapture with
    ⟨captured, capturedResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame capturedResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [inputState, State.diagnostics, List.reverse_reverse] using diagnostics
  · have carrier := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = tokens at carrier
    change output.window.endIndex = 7 at endpoint
    change output.cursor = 6 at cursor
    simp only [State.peek?, carrier, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

end Solcore.Test.SyntaxControlLeafBlockRejectionExamples
