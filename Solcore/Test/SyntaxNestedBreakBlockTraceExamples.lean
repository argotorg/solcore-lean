import Solcore.Syntax.Parser.BlockStatementTraceProperties
import Solcore.Syntax.Parser.ControlLeafDiagnosticTraceProperties

/-! Two nonempty nested block statements are composed from the actual break
leaf's five trace contracts. Explicit tokens exercise exact nested ASTs and
parent continuation without evaluating a whole parser by decision. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNestedBreakBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

abbrev innerTrace := BlockStatementTraceParses BreakStatementTraceParses
abbrev innerRejects := BlockStatementTraceRejects BreakStatementTraceParses BreakStatementTraceRejects

theorem inner_success_sound : StatementTraceSuccessSound (blockStatement breakStatement) innerTrace :=
  blockStatement_trace_success_sound breakStatement_trace_success_sound breakStatement_success_context
theorem inner_success_complete : StatementTraceSuccessComplete (blockStatement breakStatement) innerTrace :=
  blockStatement_trace_success_complete breakStatement_trace_success_complete breakStatement_success_context
theorem inner_success_context : StatementSuccessContext (blockStatement breakStatement) :=
  blockStatement_success_context breakStatement_success_context
theorem inner_reject_sound : StatementTraceRejectSound (blockStatement breakStatement) innerRejects :=
  blockStatement_trace_reject_sound breakStatement_trace_success_sound
    breakStatement_trace_reject_sound breakStatement_success_context
theorem inner_reject_complete : StatementTraceRejectComplete (blockStatement breakStatement) innerRejects :=
  blockStatement_trace_reject_complete breakStatement_trace_success_complete
    breakStatement_trace_reject_complete breakStatement_success_context

def source : SourceId := { origin := .main, path := "nested-break-trace.sol" }
def byteSpan (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def nestedTokens (secondTerminator : Symbol) : Array Token := #[
  { span := byteSpan 0 1, value := .symbol .leftBrace },
  { span := byteSpan 2 3, value := .symbol .leftBrace },
  { span := byteSpan 4 9, value := .keyword .breakKw },
  { span := byteSpan 9 10, value := .symbol .semicolon },
  { span := byteSpan 11 12, value := .symbol .rightBrace },
  { span := byteSpan 13 14, value := .symbol .leftBrace },
  { span := byteSpan 15 20, value := .keyword .breakKw },
  { span := byteSpan 20 21, value := .symbol secondTerminator },
  { span := byteSpan 22 23, value := .symbol .rightBrace },
  { span := byteSpan 24 25, value := .symbol .rightBrace },
  { span := byteSpan 26 30, value := .identifier "tail" }]
def atCursor (secondTerminator : Symbol) (endIndex cursor : Nat) : Remainder := {
  tokens := nestedTokens secondTerminator, endIndex, cursor
}
def inputState (content : String) (secondTerminator : Symbol) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content }, tokens := nestedTokens secondTerminator
  cursor := 0, window := { endIndex := 11, endByte := 30 }, diagnosticsRev := prior.reverse
}
def leftBreak : Statement := { span := byteSpan 4 10, value := .breakStmt }
def rightBreak : Statement := { span := byteSpan 15 21, value := .breakStmt }
def leftInner : Statement := { span := byteSpan 2 12, value := .block [leftBreak] }
def rightInner : Statement := { span := byteSpan 13 23, value := .block [rightBreak] }
def outerBody : Block := { span := byteSpan 0 25, value := [leftInner, rightInner] }

theorem left_inner_trace (secondTerminator : Symbol) (reportSource : SourceId)
    (endByte endIndex : Nat) (inside : 9 < endIndex) :
    innerTrace reportSource endByte (atCursor secondTerminator endIndex 1)
      leftInner (atCursor secondTerminator endIndex 5) [] := by
  have leaf : BreakStatementTraceParses reportSource endByte (atCursor secondTerminator endIndex 2)
      leftBreak (atCursor secondTerminator endIndex 4) [] :=
    ⟨.parsed (byteSpan 4 9) (byteSpan 9 10) (afterMarker := atCursor secondTerminator endIndex 3)
      ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩
      ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩
  have closing : CoreBlockItemsTraceParses BreakStatementTraceParses reportSource endByte
      (atCursor secondTerminator endIndex 4) [] (byteSpan 11 12)
      (atCursor secondTerminator endIndex 5) [] := .close _ ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩
  exact .parsed (.parsed (byteSpan 2 3) (byteSpan 11 12)
    (afterOpening := atCursor secondTerminator endIndex 2)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    (.next (by change 2 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens]) leaf
      (by change 2 < 4; decide) closing)
    (.lastRequired (.clean (statement := leftBreak) trivial)))

private theorem right_inner_trace (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 9 < endIndex) :
    innerTrace reportSource endByte (atCursor .semicolon endIndex 5)
      rightInner (atCursor .semicolon endIndex 9) [] := by
  have leaf : BreakStatementTraceParses reportSource endByte (atCursor .semicolon endIndex 6)
      rightBreak (atCursor .semicolon endIndex 8) [] :=
    ⟨.parsed (byteSpan 15 20) (byteSpan 20 21) (afterMarker := atCursor .semicolon endIndex 7)
      ⟨⟨by change 6 < endIndex; omega, rfl⟩, rfl⟩
      ⟨⟨by change 7 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩
  have closing : CoreBlockItemsTraceParses BreakStatementTraceParses reportSource endByte
      (atCursor .semicolon endIndex 8) [] (byteSpan 22 23) (atCursor .semicolon endIndex 9) [] :=
    .close _ ⟨⟨by change 8 < endIndex; omega, rfl⟩, rfl⟩
  exact .parsed (.parsed (byteSpan 13 14) (byteSpan 22 23)
    (afterOpening := atCursor .semicolon endIndex 6)
    ⟨⟨by change 5 < endIndex; omega, rfl⟩, rfl⟩
    (.next (by change 6 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens]) leaf
      (by change 6 < 8; decide) closing)
    (.lastRequired (.clean (statement := rightBreak) trivial)))

private theorem outer_trace : CoreBlockTraceParses innerTrace .require source 30
    (atCursor .semicolon 11 0) outerBody (atCursor .semicolon 11 10) [] := by
  have closing : CoreBlockItemsTraceParses innerTrace source 30 (atCursor .semicolon 11 9)
      [] (byteSpan 24 25) (atCursor .semicolon 11 10) [] := .close _ ⟨⟨by decide, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses innerTrace source 30 (atCursor .semicolon 11 5)
      [rightInner] (byteSpan 24 25) (atCursor .semicolon 11 10) [] :=
    .next (by decide) (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (right_inner_trace source 30 11 (by decide)) (by decide) closing
  have items : CoreBlockItemsTraceParses innerTrace source 30 (atCursor .semicolon 11 1)
      [leftInner, rightInner] (byteSpan 24 25) (atCursor .semicolon 11 10) [] :=
    .next (by decide) (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (left_inner_trace .semicolon source 30 11 (by decide)) (by decide) last
  exact .parsed (byteSpan 0 1) (byteSpan 24 25) (afterOpening := atCursor .semicolon 11 1)
    ⟨⟨by decide, rfl⟩, rfl⟩ items
    (.cons (.clean (statement := leftInner) trivial) (.lastRequired (.clean (statement := rightInner) trivial)))

/-- Two actual nested block statements retain all nested spans and written
order. The raw outer block stops at `tail`, with no new diagnostic event. -/
theorem nested_raw_success (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (blockStatement breakStatement) .require
        (inputState "{ { break; } { break; } } tail" .semicolon prior) = .ok outerBody output ∧
      output.declarativeRemainder = atCursor .semicolon 11 10 ∧ output.diagnostics = prior := by
  simpa only [inputState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_success_iff inner_success_sound inner_success_complete inner_success_context .require
      (input := inputState "{ { break; } { break; } } tail" .semicolon prior)).mp outer_trace

/-- Adding the outer statement wrapper preserves the same full output state,
while mapping the complete two-inner-block body into one outer block statement. -/
theorem nested_statement_success (prior : List ParseDiagnostic) :
    ∃ output, blockStatement (blockStatement breakStatement)
        (inputState "{ { break; } { break; } } tail" .semicolon prior) =
        .ok { span := outerBody.span, value := .block outerBody.value } output ∧
      output.declarativeRemainder = atCursor .semicolon 11 10 ∧ output.diagnostics = prior ∧
      output.file = (inputState "{ { break; } { break; } } tail" .semicolon prior).file ∧
      output.window = { endIndex := 11, endByte := 30 } ∧
      output.peek? = some { span := byteSpan 26 30, value := .identifier "tail" } := by
  rcases nested_raw_success prior with ⟨output, raw, after, diagnostics⟩
  have result := blockStatement_success_iff_raw.mpr ⟨outerBody, raw, rfl⟩
  have frame := blockStatement_success_context inner_success_context result
  refine ⟨output, result, after, diagnostics, frame.1, frame.2, ?_⟩
  have tokens := congrArg Remainder.tokens after
  have endpoint := congrArg Remainder.endIndex after
  have cursor := congrArg Remainder.cursor after
  change output.tokens = nestedTokens .semicolon at tokens
  change output.window.endIndex = 11 at endpoint
  change output.cursor = 10 at cursor
  simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
  rfl

end Solcore.Test.SyntaxNestedBreakBlockTraceExamples
