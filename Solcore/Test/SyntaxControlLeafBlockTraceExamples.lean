import Solcore.Syntax.Parser.ControlLeafDiagnosticTraceProperties
import Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties

/-! Actual break/continue leaves consume two complete statements inside a raw
or isolated block. Explicit token fixtures preserve exact spans, full prior
diagnostics, and the following parent token; no lexer evaluation is assumed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxControlLeafBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "control-block-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def pairTokens (marker : HardKeyword) (width : Nat) : Array Token := #[
  { span := span 0 1, value := .symbol .leftBrace },
  { span := span 2 (2 + width), value := .keyword marker },
  { span := span (2 + width) (3 + width), value := .symbol .semicolon },
  { span := span (4 + width) (4 + 2 * width), value := .keyword marker },
  { span := span (4 + 2 * width) (5 + 2 * width), value := .symbol .semicolon },
  { span := span (6 + 2 * width) (7 + 2 * width), value := .symbol .rightBrace },
  { span := span (8 + 2 * width) (12 + 2 * width), value := .identifier "tail" }]
private def pairRem (marker : HardKeyword) (width endIndex cursor : Nat) : Remainder := {
  tokens := pairTokens marker width, endIndex, cursor
}
private def pairState (marker : HardKeyword) (width : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "{ " ++ marker.spelling ++ "; " ++ marker.spelling ++ "; } tail" }
  tokens := pairTokens marker width, cursor := 0
  window := { endIndex := 7, endByte := 12 + 2 * width }, diagnosticsRev := prior.reverse
}
private def pairBody (value : StatementValue) (width : Nat) : Block := {
  span := span 0 (7 + 2 * width)
  value := [{ span := span 2 (3 + width), value },
    { span := span (4 + width) (5 + 2 * width), value }]
}

private theorem pairParsed (marker : HardKeyword) (value : StatementValue)
    (width endIndex : Nat) (inside : 5 < endIndex) (policy : CoreBlockTailPolicy)
    (terminated : ∀ location, CoreBlockStatementTerminated { span := location, value })
    (reportSource : SourceId) (endByte : Nat) :
    CoreBlockTraceParses (TerminatedControlStatementTraceParses marker value) policy
      reportSource endByte (pairRem marker width endIndex 0) (pairBody value width)
      (pairRem marker width endIndex 6) [] := by
  have first : TerminatedControlStatementTraceParses marker value reportSource endByte
      (pairRem marker width endIndex 1) { span := span 2 (3 + width), value }
      (pairRem marker width endIndex 3) [] :=
    ⟨.parsed (span 2 (2 + width)) (span (2 + width) (3 + width))
      (afterMarker := pairRem marker width endIndex 2)
      ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
      ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩
  have second : TerminatedControlStatementTraceParses marker value reportSource endByte
      (pairRem marker width endIndex 3) { span := span (4 + width) (5 + 2 * width), value }
      (pairRem marker width endIndex 5) [] :=
    ⟨.parsed (span (4 + width) (4 + 2 * width)) (span (4 + 2 * width) (5 + 2 * width))
      (afterMarker := pairRem marker width endIndex 4)
      ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩
      ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩
  have closing : CoreBlockItemsTraceParses (TerminatedControlStatementTraceParses marker value)
      reportSource endByte (pairRem marker width endIndex 5) []
      (span (6 + 2 * width) (7 + 2 * width)) (pairRem marker width endIndex 6) [] :=
    .close _ ⟨⟨inside, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses (TerminatedControlStatementTraceParses marker value)
      reportSource endByte (pairRem marker width endIndex 3)
      [{ span := span (4 + width) (5 + 2 * width), value }]
      (span (6 + 2 * width) (7 + 2 * width)) (pairRem marker width endIndex 6) [] :=
    .next (by change 3 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, pairRem, pairTokens]) second
      (by change 3 < 5; decide) closing
  have items : CoreBlockItemsTraceParses (TerminatedControlStatementTraceParses marker value)
      reportSource endByte (pairRem marker width endIndex 1) (pairBody value width).value
      (span (6 + 2 * width) (7 + 2 * width)) (pairRem marker width endIndex 6) [] :=
    .next (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, pairRem, pairTokens]) first
      (by change 1 < 3; decide) last
  have tails : CoreBlockTailsDiagnosticTrace policy (pairBody value width).value [] := by
    cases policy with
    | allow => exact .cons (.clean (terminated _)) .lastAllowed
    | require => exact .cons (.clean (terminated _)) (.lastRequired (.clean (terminated _)))
  exact .parsed (span 0 1) (span (6 + 2 * width) (7 + 2 * width))
    (afterOpening := pairRem marker width endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items tails

private def pairCapture (width : Nat) : BalancedBlockCapture := {
  span := span 0 (7 + 2 * width), endIndex := 6, endByte := 7 + 2 * width
}

private theorem pairCaptured (marker : HardKeyword) (width : Nat) :
    BalancedBlockCaptures (pairRem marker width 7 0) (pairCapture width) :=
  .captured (input := pairRem marker width 7 0) (openingSpan := span 0 1)
    (closingSpan := span (6 + 2 * width) (7 + 2 * width)) ⟨by change 0 < 7; decide, rfl⟩
    (.other (token := { span := span 2 (2 + width), value := .keyword marker })
      ⟨by change 1 < 7; decide, rfl⟩ (by simp) (by simp)
      (.other (token := { span := span (2 + width) (3 + width), value := .symbol .semicolon })
        ⟨by change 2 < 7; decide, rfl⟩ (by simp) (by simp)
        (.other (token := { span := span (4 + width) (4 + 2 * width), value := .keyword marker })
          ⟨by change 3 < 7; decide, rfl⟩ (by simp) (by simp)
          (.other (token := { span := span (4 + 2 * width) (5 + 2 * width), value := .symbol .semicolon })
            ⟨by change 4 < 7; decide, rfl⟩ (by simp) (by simp)
            (.close ⟨by change 5 < 7; decide, rfl⟩)))))

/-- Two actual break statements retain full spans and every prior diagnostic
under either tail policy, and stop before the parent token following the block. -/
theorem break_pair_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock breakStatement policy (pairState .breakKw 5 prior) =
        .ok (pairBody .breakStmt 5) output ∧
      output.declarativeRemainder = pairRem .breakKw 5 7 6 ∧ output.diagnostics = prior := by
  simpa only [pairState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_success_iff breakStatement_trace_success_sound breakStatement_trace_success_complete
      breakStatement_success_context policy (input := pairState .breakKw 5 prior)).mp
      (pairParsed .breakKw .breakStmt 5 7 (by decide) policy.declarative (fun _ => trivial) _ _)

theorem continue_pair_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock continueStatement policy (pairState .continueKw 8 prior) =
        .ok (pairBody .continueStmt 8) output ∧
      output.declarativeRemainder = pairRem .continueKw 8 7 6 ∧ output.diagnostics = prior := by
  simpa only [pairState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_success_iff continueStatement_trace_success_sound
      continueStatement_trace_success_complete continueStatement_success_context policy
      (input := pairState .continueKw 8 prior)).mp
      (pairParsed .continueKw .continueStmt 8 7 (by decide) policy.declarative (fun _ => trivial) _ _)

/-- Captured success uses a child ending at byte 17 and resumes after its
closing token, retaining the original seven-token parent carrier. -/
theorem break_pair_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock breakStatement policy) (pairState .breakKw 5 prior) =
        .ok (pairBody .breakStmt 5) output ∧
      output.declarativeRemainder = pairRem .breakKw 5 7 6 ∧ output.diagnostics = prior := by
  simpa only [pairState, State.diagnostics, List.reverse_reverse, List.append_nil,
    pairRem, pairCapture, BalancedBlockCapture.parentRemainder, State.declarativeRemainder] using
    (isolatedCoreBlock_trace_success_iff (statement := breakStatement)
      breakStatement_trace_success_sound breakStatement_trace_reject_sound
      breakStatement_trace_success_complete breakStatement_trace_reject_complete
      breakStatement_success_context policy (input := pairState .breakKw 5 prior)).mp
      (.captured (pairCaptured .breakKw 5)
        (pairParsed .breakKw .breakStmt 5 6 (by decide) policy.declarative (fun _ => trivial) _ _))

theorem continue_pair_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock continueStatement policy) (pairState .continueKw 8 prior) =
        .ok (pairBody .continueStmt 8) output ∧
      output.declarativeRemainder = pairRem .continueKw 8 7 6 ∧ output.diagnostics = prior := by
  simpa only [pairState, State.diagnostics, List.reverse_reverse, List.append_nil,
    pairRem, pairCapture, BalancedBlockCapture.parentRemainder, State.declarativeRemainder] using
    (isolatedCoreBlock_trace_success_iff (statement := continueStatement)
      continueStatement_trace_success_sound continueStatement_trace_reject_sound
      continueStatement_trace_success_complete continueStatement_trace_reject_complete
      continueStatement_success_context policy (input := pairState .continueKw 8 prior)).mp
      (.captured (pairCaptured .continueKw 8)
        (pairParsed .continueKw .continueStmt 8 6 (by decide) policy.declarative (fun _ => trivial) _ _))

end Solcore.Test.SyntaxControlLeafBlockTraceExamples
