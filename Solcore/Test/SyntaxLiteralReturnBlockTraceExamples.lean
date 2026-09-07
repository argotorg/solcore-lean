import Solcore.Test.SyntaxLiteralReturnTraceExamples
import Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties

/-! A return-only block uses the actual decimal-literal expression leaf and
the empty-return bypass. This is a restricted composition, not general Core
expression or statement trace completeness. Tokens are explicitly constructed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLiteralReturnBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxLiteralReturnTraceExamples

def blockTokens : List Token := [
  { span := byteSpan 0 1, value := .symbol .leftBrace },
  marker 2, decimal 9, semicolon 11, marker 13, semicolon 19,
  { span := byteSpan 21 22, value := .symbol .rightBrace },
  { span := byteSpan 23 27, value := .identifier "tail" }]
def blockRem (endIndex cursor : Nat) : Remainder := { tokens := blockTokens.toArray, endIndex, cursor }
def firstReturn : Statement := { span := byteSpan 2 12, value := .returnStmt (some (literal42 9)) }
def lastReturn : Statement := { span := byteSpan 13 20, value := .returnStmt none }
def body : Block := { span := byteSpan 0 22, value := [firstReturn, lastReturn] }
def blockInput (prior : List ParseDiagnostic) : State := initial "{ return 42; return; } tail" blockTokens prior

private theorem firstParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 6 < endIndex) :
    ReturnStatementTraceParses LiteralExpressionTraceParses reportSource endByte
      (blockRem endIndex 1) firstReturn (blockRem endIndex 4) [] :=
  .parsed (byteSpan 2 8) (byteSpan 11 12)
    (afterMarker := blockRem endIndex 2) (afterValue := blockRem endIndex 3)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, blockRem, blockTokens, decimal])
      (literal42_trace 9 reportSource endByte ⟨by change 2 < endIndex; omega, rfl⟩))
    ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩

private theorem lastParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 6 < endIndex) :
    ReturnStatementTraceParses LiteralExpressionTraceParses reportSource endByte
      (blockRem endIndex 4) lastReturn (blockRem endIndex 6) [] :=
  .parsed (byteSpan 13 19) (byteSpan 19 20)
    (afterMarker := blockRem endIndex 5) (afterValue := blockRem endIndex 5)
    ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩
    (.absent (byteSpan 19 20) ⟨by change 5 < endIndex; omega, rfl⟩)
    ⟨⟨by change 5 < endIndex; omega, rfl⟩, rfl⟩

private theorem blockParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 6 < endIndex) (policy : CoreBlockTailPolicy) :
    CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy
      reportSource endByte (blockRem endIndex 0) body (blockRem endIndex 7) [] := by
  have closing : CoreBlockItemsTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses)
      reportSource endByte (blockRem endIndex 6) [] (byteSpan 21 22) (blockRem endIndex 7) [] :=
    .close _ ⟨⟨inside, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses)
      reportSource endByte (blockRem endIndex 4) [lastReturn] (byteSpan 21 22)
      (blockRem endIndex 7) [] :=
    .next (by change 4 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, blockRem, blockTokens, marker])
      (lastParsed reportSource endByte endIndex inside) (by change 4 < 6; decide) closing
  have items : CoreBlockItemsTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses)
      reportSource endByte (blockRem endIndex 1) [firstReturn, lastReturn] (byteSpan 21 22)
      (blockRem endIndex 7) [] :=
    .next (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, blockRem, blockTokens, marker])
      (firstParsed reportSource endByte endIndex inside) (by change 1 < 4; decide) last
  have tails : CoreBlockTailsDiagnosticTrace policy [firstReturn, lastReturn] [] := by
    have firstClean : CoreBlockStatementDiagnosticTrace firstReturn [] := .clean trivial
    have lastClean : CoreBlockStatementDiagnosticTrace lastReturn [] := .clean trivial
    cases policy with
    | allow => exact .cons firstClean .lastAllowed
    | require => exact .cons firstClean (.lastRequired lastClean)
  exact .parsed (byteSpan 0 1) (byteSpan 21 22) (afterOpening := blockRem endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items tails

private def capture : BalancedBlockCapture := { span := byteSpan 0 22, endIndex := 7, endByte := 22 }

private theorem blockCaptured : BalancedBlockCaptures (blockRem 8 0) capture :=
  .captured (input := blockRem 8 0) (openingSpan := byteSpan 0 1) (closingSpan := byteSpan 21 22)
    ⟨by decide, rfl⟩
    (.other (token := marker 2) ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := decimal 9) ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := semicolon 11) ⟨by decide, rfl⟩ (by decide) (by decide)
          (.other (token := marker 13) ⟨by decide, rfl⟩ (by decide) (by decide)
            (.other (token := semicolon 19) ⟨by decide, rfl⟩ (by decide) (by decide)
              (.close ⟨by decide, rfl⟩))))))

/-- The actual return constructor uses the actual literal leaf for the first
value and bypasses it for the second return. Both full ASTs remain ordered. -/
theorem literal_and_empty_returns_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (returnStatement literalExpression) policy (blockInput prior) = .ok body output ∧
      output.declarativeRemainder = blockRem 8 7 ∧ output.diagnostics = prior := by
  simpa only [blockInput, initial, State.initial, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_success_iff (returnStatement_trace_success_sound literalExpression_trace_success_sound)
      (returnStatement_trace_success_complete literalExpression_trace_success_complete)
      (returnStatement_success_context literalExpression_success_context) policy
      (input := blockInput prior)).mp (blockParsed source 27 8 (by decide) policy.declarative)

/-- Balanced success restores the full parent window and leaves `tail`
unread after the mixed nonempty/empty return body, with every prior event intact. -/
theorem literal_and_empty_returns_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock (returnStatement literalExpression) policy) (blockInput prior) =
        .ok body output ∧ output.declarativeRemainder = blockRem 8 7 ∧ output.diagnostics = prior ∧
      output.file = (blockInput prior).file ∧ output.window = (blockInput prior).window ∧
      output.peek? = some { span := byteSpan 23 27, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses
      (CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
        (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects) policy.declarative)
      source 27 (blockRem 8 0) body (blockRem 8 7) [] :=
    .captured blockCaptured (blockParsed source 22 7 (by decide) policy.declarative)
  rcases (isolatedCoreBlock_trace_success_iff (statement := returnStatement literalExpression)
      (returnStatement_trace_success_sound literalExpression_trace_success_sound)
      (returnStatement_reject_trace_sound literalExpression_trace_success_sound
        literalExpression_trace_reject_sound literalExpression_success_context)
      (returnStatement_trace_success_complete literalExpression_trace_success_complete)
      (returnStatement_trace_reject_complete literalExpression_trace_success_complete
        literalExpression_trace_reject_complete literalExpression_success_context)
      (returnStatement_success_context literalExpression_success_context) policy
      (input := blockInput prior)).mp parsed with ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := blockInput prior) blockCaptured with
    ⟨captured, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [blockInput, initial, State.initial, State.diagnostics,
      List.reverse_reverse, List.append_nil] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = blockTokens.toArray at tokens
    change output.window.endIndex = 8 at endpoint
    change output.cursor = 7 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

end Solcore.Test.SyntaxLiteralReturnBlockTraceExamples
