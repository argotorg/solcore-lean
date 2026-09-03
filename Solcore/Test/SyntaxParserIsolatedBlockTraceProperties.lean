import Solcore.Syntax.Parser.IsolatedBlockTraceCompletenessProperties

/-! Conditional isolation-trace consumers. Inner contracts are visible and no
example asserts that the concrete Core parser already has a full trace grammar.
All parent diagnostics and inner/parent byte boundaries remain unrestricted. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserIsolatedBlockTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {parser : Parser Block}
  {blockParses : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  (successSound : BlockTraceSuccessSound parser blockParses)
  (rejectSound : BlockTraceRejectSound parser blockRejects)
  (successComplete : BlockTraceSuccessComplete parser blockParses)
  (rejectComplete : BlockTraceRejectComplete parser blockRejects)

example : BlockTraceSuccessSound (isolateBlock parser)
    (IsolatedBlockTraceParses blockParses blockRejects) :=
  isolateBlock_success_trace_sound successSound rejectSound

example : BlockTraceRejectSound (isolateBlock parser)
    (IsolatedBlockTraceRejects blockRejects) :=
  isolateBlock_reject_trace_sound rejectSound

example : BlockTraceSuccessComplete (isolateBlock parser)
    (IsolatedBlockTraceParses blockParses blockRejects) :=
  isolateBlock_success_trace_complete successComplete rejectComplete

example : BlockTraceRejectComplete (isolateBlock parser)
    (IsolatedBlockTraceRejects blockRejects) :=
  isolateBlock_reject_trace_complete rejectComplete

example {input : State} {body : Block} {after : Remainder} {trace : List ParseDiagnostic} :
    IsolatedBlockTraceParses blockParses blockRejects input.file.id input.window.endByte
      input.declarativeRemainder body after trace ↔
      ∃ output, isolateBlock parser input = .ok body output ∧
        output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_trace_success_iff successSound rejectSound successComplete rejectComplete

example {input : State} {after : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    IsolatedBlockTraceRejects blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace ↔
      ∃ failure output, isolateBlock parser input = .reject failure output ∧
        output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
        output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_trace_reject_iff rejectSound rejectComplete

include successSound rejectSound in
/-- Soundness guarantees some complete suffix for every success, even before
any trace is proposed. Nonempty prior diagnostics do not invalidate the claim. -/
theorem every_success_has_an_independent_suffix
    {input output : State} {body : Block}
    (result : isolateBlock parser input = .ok body output) :
    ∃ trace, IsolatedBlockTraceParses blockParses blockRejects
      input.file.id input.window.endByte input.declarativeRemainder body
      output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_success_trace_sound successSound rejectSound result

include successComplete rejectComplete in
/-- The captured child uses the closing brace's byte endpoint, not the parent
window endpoint. Its own final cursor does not determine the resumed parent. -/
theorem captured_success_uses_child_context
    {input : State} {capture : BalancedBlockCapture} {childAfter : Remainder}
    {body : Block} {trace : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input.declarativeRemainder capture)
    (bodyParsed : blockParses input.file.id capture.endByte
      (capture.childRemainder input.declarativeRemainder) body childAfter trace) :
    ∃ output, isolateBlock parser input = .ok body output ∧
      output.declarativeRemainder = capture.parentRemainder input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_success_trace_complete successComplete rejectComplete (.captured captured bodyParsed)

include successComplete rejectComplete in
/-- Ordinary child rejection contributes the exact report once after child
events, restores the complete parent frame, and returns only an empty block. -/
theorem captured_rejection_restores_parent_and_commits_once
    {input : State} {capture : BalancedBlockCapture} {childAfter : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (captured : BalancedBlockCaptures input.declarativeRemainder capture)
    (bodyRejected : blockRejects input.file.id capture.endByte
      (capture.childRemainder input.declarativeRemainder) childAfter diagnostic trace) :
    ∃ output, isolateBlock parser input = .ok { span := capture.span, value := [] } output ∧
      output.declarativeRemainder = capture.parentRemainder input.declarativeRemainder ∧
      output.diagnostics = input.diagnostics ++ (trace ++ [diagnostic]) ∧
      output.file = input.file ∧ output.tokens = input.tokens ∧
      output.window = input.window ∧ output.cursor = capture.endIndex := by
  rcases isolateBlock_success_trace_complete successComplete rejectComplete
      (.recovered captured bodyRejected) with ⟨output, result, remainderEq, traceEq⟩
  rcases BlockInternals.captureBlock?_complete captured with
    ⟨executableCapture, captureResult, _, endIndexEq, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  exact ⟨output, result, remainderEq, traceEq, frame.1, frame.2.1,
    frame.2.2.1, frame.2.2.2.trans endIndexEq⟩

include rejectComplete in
/-- With no balanced capture, a rejection escapes with the child's report
still uncommitted; no singleton is added to the preceding diagnostic suffix. -/
theorem uncaptured_rejection_preserves_uncommitted_report
    {input : State} {after : Remainder} {diagnostic : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (absent : BalancedBlockCaptureAbsentAt input.declarativeRemainder)
    (bodyRejected : blockRejects input.file.id input.window.endByte
      input.declarativeRemainder after diagnostic trace) :
    ∃ failure output, isolateBlock parser input = .reject failure output ∧
      output.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      output.diagnostics = input.diagnostics ++ trace :=
  isolateBlock_reject_trace_complete rejectComplete (.direct absent bodyRejected)

end Solcore.Test.SyntaxParserIsolatedBlockTraceProperties
