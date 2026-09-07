import Solcore.Test.SyntaxNestedBreakBlockTraceExamples
import Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties

/-! The second nested break rejects at its plus token. Both statement wrappers
propagate that raw failure; one outer isolation recovers exactly once. The
explicit balanced scan crosses two nested brace pairs before restoring `tail`. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNestedBreakBlockRejectionExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxNestedBreakBlockTraceExamples

private def rejectedInput (prior : List ParseDiagnostic) : State :=
  inputState "{ { break; } { break+ } } tail" .plus prior
private def semicolonFailure : Failure := {
  span := byteSpan 20 21, found := some (.symbol .plus)
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}
private def capture : BalancedBlockCapture := {
  span := byteSpan 0 25, endIndex := 10, endByte := 25
}

private theorem right_inner_rejected (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 9 < endIndex) :
    innerRejects reportSource endByte (atCursor .plus endIndex 5)
      (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] := by
  have leaf : BreakStatementTraceRejects reportSource endByte (atCursor .plus endIndex 6)
      (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] :=
    .semicolonMissing (byteSpan 15 20)
      ⟨⟨by change 6 < endIndex; omega, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (.reported (.token (current := { span := byteSpan 20 21, value := .symbol .plus })
        ⟨by change 7 < endIndex; omega, rfl⟩))
  have item : CoreBlockItemsTraceRejects BreakStatementTraceParses BreakStatementTraceRejects
      reportSource endByte (atCursor .plus endIndex 6)
      (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] :=
    .statementRejected (by change 6 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens]) leaf
  exact .rejected (.itemsRejected (byteSpan 13 14) (afterOpening := atCursor .plus endIndex 6)
    ⟨⟨by change 5 < endIndex; omega, rfl⟩, rfl⟩ item)

private theorem outer_rejected (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 9 < endIndex) :
    CoreBlockTraceRejects innerTrace innerRejects .require reportSource endByte
      (atCursor .plus endIndex 0) (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] := by
  have last : CoreBlockItemsTraceRejects innerTrace innerRejects reportSource endByte
      (atCursor .plus endIndex 5) (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] :=
    .statementRejected (by change 5 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (right_inner_rejected reportSource endByte endIndex inside)
  have items : CoreBlockItemsTraceRejects innerTrace innerRejects reportSource endByte
      (atCursor .plus endIndex 1) (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] :=
    .laterRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (left_inner_trace .plus reportSource endByte endIndex inside) (by change 1 < 5; decide) last
  exact .itemsRejected (byteSpan 0 1) (afterOpening := atCursor .plus endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items

private theorem balanced_capture : BalancedBlockCaptures (atCursor .plus 11 0) capture :=
  .captured (input := atCursor .plus 11 0) (openingSpan := byteSpan 0 1)
    (closingSpan := byteSpan 24 25) ⟨by decide, rfl⟩
    (.opening (openingSpan := byteSpan 2 3) ⟨by decide, rfl⟩
      (.other (token := { span := byteSpan 4 9, value := .keyword .breakKw })
        ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := { span := byteSpan 9 10, value := .symbol .semicolon })
          ⟨by decide, rfl⟩ (by decide) (by decide)
          (.nestedClosing (nestedSpan := byteSpan 11 12) ⟨by decide, rfl⟩
            (.opening (openingSpan := byteSpan 13 14) ⟨by decide, rfl⟩
              (.other (token := { span := byteSpan 15 20, value := .keyword .breakKw })
                ⟨by decide, rfl⟩ (by decide) (by decide)
                (.other (token := { span := byteSpan 20 21, value := .symbol .plus })
                  ⟨by decide, rfl⟩ (by decide) (by decide)
                  (.nestedClosing (nestedSpan := byteSpan 22 23) ⟨by decide, rfl⟩
                    (.close ⟨by decide, rfl⟩)))))))))

/-- The actual inner statement has no isolation: the second break's missing
semicolon escapes both raw blocks at cursor 7, without committing its report. -/
theorem nested_raw_rejects_at_inner_plus (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (blockStatement breakStatement) .require (rejectedInput prior) =
        .reject semicolonFailure output ∧
      output.declarativeRemainder = atCursor .plus 11 7 ∧ output.diagnostics = prior := by
  simpa only [rejectedInput, inputState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_reject_failure_iff inner_success_sound inner_reject_sound
      inner_success_complete inner_reject_complete inner_success_context .require
      (input := rejectedInput prior)).mp (outer_rejected source 30 11 (by decide))

/-- A second statement wrapper retains the identical failure and full output
state. Neither nested closing brace nor the outer closing brace is consumed. -/
theorem nested_statement_rejects_without_skipping (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (blockStatement breakStatement) .require (rejectedInput prior) =
        .reject semicolonFailure output ∧
      blockStatement (blockStatement breakStatement) (rejectedInput prior) =
        .reject semicolonFailure output ∧
      output.declarativeRemainder = atCursor .plus 11 7 ∧ output.diagnostics = prior ∧
      output.peek? = some { span := byteSpan 20 21, value := .symbol .plus } := by
  rcases nested_raw_rejects_at_inner_plus prior with ⟨output, raw, after, diagnostics⟩
  refine ⟨output, raw, blockStatement_reject_iff_raw.mpr raw, after, diagnostics, ?_⟩
  have tokens := congrArg Remainder.tokens after
  have endpoint := congrArg Remainder.endIndex after
  have cursor := congrArg Remainder.cursor after
  change output.tokens = nestedTokens .plus at tokens
  change output.window.endIndex = 11 at endpoint
  change output.cursor = 7 at cursor
  simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
  rfl

/-- Only the outer wrapper isolates. It drops the unfinished nested body and
appends one report, restoring the byte-30 parent after its byte-25 child window. -/
theorem one_outer_isolation_recovers_once (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock (blockStatement breakStatement) .require) (rejectedInput prior) =
        .ok { span := byteSpan 0 25, value := [] } output ∧
      output.declarativeRemainder = atCursor .plus 11 10 ∧
      output.diagnostics = prior ++ [semicolonFailure.toDiagnostic] ∧
      output.file = (rejectedInput prior).file ∧ output.window = (rejectedInput prior).window ∧
      output.peek? = some { span := byteSpan 26 30, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses (CoreBlockTraceParses innerTrace .require)
      (CoreBlockTraceRejects innerTrace innerRejects .require) source 30 (atCursor .plus 11 0)
      { span := byteSpan 0 25, value := [] } (atCursor .plus 11 10) [semicolonFailure.toDiagnostic] :=
    .recovered balanced_capture (outer_rejected source 25 10 (by decide))
  rcases (isolatedCoreBlock_trace_success_iff (statement := blockStatement breakStatement)
      inner_success_sound inner_reject_sound inner_success_complete inner_reject_complete
      inner_success_context .require (input := rejectedInput prior)).mp parsed with
    ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := rejectedInput prior) balanced_capture with
    ⟨captured, capturedResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame capturedResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [rejectedInput, inputState, State.diagnostics, List.reverse_reverse] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = nestedTokens .plus at tokens
    change output.window.endIndex = 11 at endpoint
    change output.cursor = 10 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

end Solcore.Test.SyntaxNestedBreakBlockRejectionExamples
