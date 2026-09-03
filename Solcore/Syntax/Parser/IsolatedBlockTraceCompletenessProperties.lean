import Solcore.Syntax.Parser.IsolatedBlockTraceSoundnessProperties

/-! Independent isolation traces execute under explicit inner trace contracts.
The final correspondences retain source context, AST/report, remainder, and the
complete appended trace, without claiming concrete Core trace completeness. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {parser : Parser Block}
  {blockParses : SourceId → Nat → DeclarativeGrammar.Remainder → Block →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem captureBlock?_eq_none_of_absent {input : State}
    (absent : DeclarativeGrammar.BalancedBlockCaptureAbsentAt input.declarativeRemainder) :
    BlockInternals.captureBlock? input = none := by
  cases found : BlockInternals.captureBlock? input with
  | none => rfl
  | some captured =>
      rcases BlockInternals.captureBlock?_success_sound found with
        ⟨capture, captured, _, _, _⟩
      exact False.elim (absent ⟨capture, captured⟩)

/-- Every independent isolated success executes. Captured rejection restores
the parent remainder and emits its uncommitted report after the child trace. -/
theorem isolateBlock_success_trace_complete
    (successComplete : BlockTraceSuccessComplete parser blockParses)
    (rejectComplete : BlockTraceRejectComplete parser blockRejects)
    {input : State} {body : Block} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.IsolatedBlockTraceParses blockParses blockRejects
      input.file.id input.window.endByte input.declarativeRemainder body after trace) :
    ∃ output, isolateBlock parser input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases parsed with
  | direct absent bodyParsed =>
      rw [isolateBlock_eq_of_no_capture parser (captureBlock?_eq_none_of_absent absent)]
      exact successComplete bodyParsed
  | captured captureParsed bodyParsed =>
      rename_i childOutput capture
      rcases BlockInternals.captureBlock?_complete captureParsed with
        ⟨captured, capturedResult, _spanEq, endIndexEq, endByteEq⟩
      have childParsed : blockParses
          (input.enterWindow input.cursor captured.window).file.id
          (input.enterWindow input.cursor captured.window).window.endByte
          (input.enterWindow input.cursor captured.window).declarativeRemainder
          body childOutput trace := by
        simpa only [State.enterWindow, State.declarativeRemainder,
          DeclarativeGrammar.BalancedBlockCapture.childRemainder, endIndexEq, endByteEq]
          using bodyParsed
      rcases successComplete childParsed with ⟨childAfter, childResult, _, traceEq⟩
      refine ⟨_, (isolateBlock_captured_success_trace capturedResult childResult).1, ?_, ?_⟩
      · simp only [State.mergeDiagnostics, State.declarativeRemainder,
          DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]
      · rw [(isolateBlock_captured_success_trace capturedResult childResult).2, traceEq]
        simp only [State.enterWindow_diagnostics_eq_nil, List.nil_append]
  | recovered captureParsed bodyRejected =>
      rename_i childRejected capture diagnostic childTrace
      rcases BlockInternals.captureBlock?_complete captureParsed with
        ⟨captured, capturedResult, spanEq, endIndexEq, endByteEq⟩
      have childTraceRejected : blockRejects
          (input.enterWindow input.cursor captured.window).file.id
          (input.enterWindow input.cursor captured.window).window.endByte
          (input.enterWindow input.cursor captured.window).declarativeRemainder
          childRejected diagnostic childTrace := by
        simpa only [State.enterWindow, State.declarativeRemainder,
          DeclarativeGrammar.BalancedBlockCapture.childRemainder, endIndexEq, endByteEq]
          using bodyRejected
      rcases rejectComplete childTraceRejected with
        ⟨failure, childAfter, childResult, _, reportEq, traceEq⟩
      refine ⟨((({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics
        childAfter).emit failure.toDiagnostic), ?_, ?_, ?_⟩
      · simpa only [spanEq] using
          (isolateBlock_captured_reject_trace capturedResult childResult).1
      · simp only [State.mergeDiagnostics, State.emit, State.declarativeRemainder,
          DeclarativeGrammar.BalancedBlockCapture.parentRemainder, endIndexEq]
      · rw [(isolateBlock_captured_reject_trace capturedResult childResult).2, traceEq, reportEq]
        simp only [State.enterWindow_diagnostics_eq_nil, List.nil_append, List.append_assoc]

/-- Uncaptured independent rejection escapes unchanged, with the same report
and remainder and without prematurely committing the final diagnostic. -/
theorem isolateBlock_reject_trace_complete
    (rejectComplete : BlockTraceRejectComplete parser blockRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejected : DeclarativeGrammar.IsolatedBlockTraceRejects blockRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace) :
    ∃ failure output, isolateBlock parser input = .reject failure output ∧
      output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace := by
  cases rejected with
  | direct absent bodyRejected =>
      rw [isolateBlock_eq_of_no_capture parser (captureBlock?_eq_none_of_absent absent)]
      exact rejectComplete bodyRejected

/-- Exact success correspondence requires both directions of both inner
ordinary outcomes, since captured rejection is an outer success. Soundness
supplies a suffix for every result; append cancellation identifies that suffix. -/
theorem isolateBlock_trace_success_iff
    (successSound : BlockTraceSuccessSound parser blockParses)
    (rejectSound : BlockTraceRejectSound parser blockRejects)
    (successComplete : BlockTraceSuccessComplete parser blockParses)
    (rejectComplete : BlockTraceRejectComplete parser blockRejects)
    {input : State} {body : Block} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IsolatedBlockTraceParses blockParses blockRejects
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
      ∃ output, isolateBlock parser input = .ok body output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact isolateBlock_success_trace_complete successComplete rejectComplete
  · rintro ⟨output, result, remainderEq, traceEq⟩
    rcases isolateBlock_success_trace_sound successSound rejectSound result with
      ⟨actual, parsed, actualEq⟩
    have same : actual = trace := List.append_cancel_left (actualEq.symm.trans traceEq)
    simpa only [remainderEq, same] using parsed

/-- Escaping rejection needs only the two inner rejection contracts. Failure
records are compared through their complete diagnostic, never by assumption. -/
theorem isolateBlock_trace_reject_iff
    (rejectSound : BlockTraceRejectSound parser blockRejects)
    (rejectComplete : BlockTraceRejectComplete parser blockRejects)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.IsolatedBlockTraceRejects blockRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
      ∃ failure output, isolateBlock parser input = .reject failure output ∧
        output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact isolateBlock_reject_trace_complete rejectComplete
  · rintro ⟨failure, output, result, remainderEq, reportEq, traceEq⟩
    rcases isolateBlock_reject_trace_sound rejectSound result with
      ⟨actual, rejected, actualEq⟩
    have same : actual = trace := List.append_cancel_left (actualEq.symm.trans traceEq)
    simpa only [remainderEq, reportEq, same] using rejected

end Solcore.Syntax.Parser
