import Solcore.Syntax.Parser.BlockDiagnosticTraceContracts
import Solcore.Syntax.Parser.BalancedBlockCaptureCompletenessProperties
import Solcore.Syntax.Parser.BalancedBlockCaptureSoundnessProperties
import Solcore.Syntax.Parser.IsolatedBlockDiagnosticTraceProperties

/-! Independent isolation traces from executable results, conditional on
explicit inner-parser trace soundness, including existence of every suffix. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {parser : Parser Block}
  {blockParses : SourceId → Nat → DeclarativeGrammar.Remainder → Block →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- Every isolation success is a direct success, captured success, or recovered
ordinary rejection. The child starts with no prior diagnostic events. -/
theorem isolateBlock_success_trace_sound
    (successSound : BlockTraceSuccessSound parser blockParses)
    (rejectSound : BlockTraceRejectSound parser blockRejects)
    {input output : State} {body : Block}
    (result : isolateBlock parser input = .ok body output) :
    ∃ trace, DeclarativeGrammar.IsolatedBlockTraceParses blockParses blockRejects
      input.file.id input.window.endByte input.declarativeRemainder body
      output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases capturedResult : BlockInternals.captureBlock? input with
  | none =>
      rw [isolateBlock_eq_of_no_capture parser capturedResult] at result
      rcases successSound result with ⟨trace, bodyParsed, traceEq⟩
      exact ⟨trace, .direct (BlockInternals.captureBlock?_none_absent capturedResult)
        bodyParsed, traceEq⟩
  | some captured =>
      rcases BlockInternals.captureBlock?_success_sound capturedResult with
        ⟨capture, captureParsed, spanEq, endIndexEq, endByteEq⟩
      rcases (isolateBlock_captured_success_iff capturedResult).mp result with
        ⟨childAfter, childResult, rfl⟩ | ⟨failure, childAfter, childResult, rfl, rfl⟩
      · rcases successSound childResult with ⟨trace, bodyParsed, traceEq⟩
        have childParsed : blockParses input.file.id capture.endByte
            (capture.childRemainder input.declarativeRemainder) body
            childAfter.declarativeRemainder trace := by
          simpa only [State.enterWindow, State.declarativeRemainder,
            DeclarativeGrammar.BalancedBlockCapture.childRemainder,
            endIndexEq, endByteEq] using bodyParsed
        refine ⟨trace, ?_, ?_⟩
        · simpa only [State.mergeDiagnostics, State.declarativeRemainder,
            DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]
            using DeclarativeGrammar.IsolatedBlockTraceParses.captured captureParsed childParsed
        · rw [(isolateBlock_captured_success_trace capturedResult childResult).2, traceEq]
          simp only [State.enterWindow_diagnostics_eq_nil, List.nil_append]
      · rcases rejectSound childResult with ⟨trace, bodyRejected, traceEq⟩
        have childRejected : blockRejects input.file.id capture.endByte
            (capture.childRemainder input.declarativeRemainder)
            childAfter.declarativeRemainder failure.toDiagnostic trace := by
          simpa only [State.enterWindow, State.declarativeRemainder,
            DeclarativeGrammar.BalancedBlockCapture.childRemainder,
            endIndexEq, endByteEq] using bodyRejected
        refine ⟨trace ++ [failure.toDiagnostic], ?_, ?_⟩
        · simpa only [State.mergeDiagnostics, State.emit, State.declarativeRemainder,
            DeclarativeGrammar.BalancedBlockCapture.parentRemainder, spanEq, endIndexEq]
            using DeclarativeGrammar.IsolatedBlockTraceParses.recovered captureParsed childRejected
        · rw [(isolateBlock_captured_reject_trace capturedResult childResult).2, traceEq]
          simp only [State.enterWindow_diagnostics_eq_nil, List.nil_append, List.append_assoc]

/-- Only the no-capture branch can reject. Its report remains uncommitted and
its original preceding trace is appended unchanged to the parent diagnostics. -/
theorem isolateBlock_reject_trace_sound
    (rejectSound : BlockTraceRejectSound parser blockRejects)
    {input rejected : State} {failure : Failure}
    (result : isolateBlock parser input = .reject failure rejected) :
    ∃ trace, DeclarativeGrammar.IsolatedBlockTraceRejects blockRejects
      input.file.id input.window.endByte input.declarativeRemainder
      rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  cases capturedResult : BlockInternals.captureBlock? input with
  | none =>
      rw [isolateBlock_eq_of_no_capture parser capturedResult] at result
      rcases rejectSound result with ⟨trace, bodyRejected, traceEq⟩
      exact ⟨trace, .direct (BlockInternals.captureBlock?_none_absent capturedResult)
        bodyRejected, traceEq⟩
  | some captured =>
      exact False.elim (isolateBlock_captured_ne_reject capturedResult result)

end Solcore.Syntax.Parser
