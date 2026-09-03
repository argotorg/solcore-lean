import Solcore.Syntax.Parser.Block

/-! Compositional laws from executable child outcomes, not independent grammar
judgments. Balanced isolation resets child diagnostics and restores the parent. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Entering any child window starts a fresh diagnostic sequence. -/
theorem State.enterWindow_diagnostics_eq_nil
    (input : State) (startIndex : Nat) (window : TokenWindow) :
    (input.enterWindow startIndex window).diagnostics = [] := rfl

/-- Merging preserves every event, including duplicates, in parent-child order. -/
theorem State.mergeDiagnostics_diagnostics_eq_append (parent child : State) :
    (parent.mergeDiagnostics child).diagnostics = parent.diagnostics ++ child.diagnostics := by
  simp only [State.mergeDiagnostics, State.diagnostics, List.reverse_append]

/-- Without a balanced capture, isolation is exactly the underlying parser,
including its successful value, rejected state, or invariant failure. -/
theorem isolateBlock_eq_of_no_capture (parser : Parser Block) {input : State}
    (notCaptured : BlockInternals.captureBlock? input = none) :
    isolateBlock parser input = parser input := by
  simp only [isolateBlock, notCaptured]

/-- Captured success retains the child AST but restores the parent carrier
and cursor boundary, merging the complete child trace after the parent's. -/
theorem isolateBlock_captured_success_trace
    {parser : Parser Block} {input childAfter : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .ok body childAfter) :
    isolateBlock parser input = .ok body
        (({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter) ∧
      (({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter).diagnostics =
        input.diagnostics ++ childAfter.diagnostics := by
  refine ⟨by simp only [isolateBlock, capture, childResult], ?_⟩
  exact State.mergeDiagnostics_diagnostics_eq_append _ _

/-- Captured ordinary rejection recovers an empty body at the captured span.
Its exact failure report is committed once, after parent and child events. -/
theorem isolateBlock_captured_reject_trace
    {parser : Parser Block} {input childAfter : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter) :
    isolateBlock parser input = .ok { span := captured.span, value := [] }
        ((({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter).emit
          failure.toDiagnostic) ∧
      ((({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter).emit
        failure.toDiagnostic).diagnostics =
        input.diagnostics ++ childAfter.diagnostics ++ [failure.toDiagnostic] := by
  refine ⟨by simp only [isolateBlock, capture, childResult], ?_⟩
  simp only [State.emit, State.mergeDiagnostics, State.diagnostics,
    List.reverse_cons, List.reverse_append]

/-- Invariants remain invariants; they do not become empty-body recovery. -/
theorem isolateBlock_captured_invariant_iff
    {parser : Parser Block} {input : State} {error : ParserInvariantError}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured) :
    isolateBlock parser input = .invariant error ↔
      parser (input.enterWindow input.cursor captured.window) = .invariant error := by
  simp only [isolateBlock, capture]
  cases childResult : parser (input.enterWindow input.cursor captured.window) <;> simp

/-- Exact captured-success classification separates ordinary child success
from recovered child rejection; the two cases retain their exact states. -/
theorem isolateBlock_captured_success_iff
    {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured) :
    isolateBlock parser input = .ok body output ↔
      (∃ childAfter,
        parser (input.enterWindow input.cursor captured.window) = .ok body childAfter ∧
        output = ({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics childAfter) ∨
      (∃ failure childAfter,
        parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter ∧
        body = { span := captured.span, value := [] } ∧
        output = (({ input with cursor := captured.window.endIndex } : State).mergeDiagnostics
          childAfter).emit failure.toDiagnostic) := by
  constructor
  · intro result
    simp only [isolateBlock, capture] at result
    cases childResult : parser (input.enterWindow input.cursor captured.window) with
    | invariant error => simp [childResult] at result
    | ok childBody childAfter =>
        simp only [childResult] at result
        cases result
        exact .inl ⟨childAfter, rfl, rfl⟩
    | reject failure childAfter =>
        simp only [childResult] at result
        cases result
        exact .inr ⟨failure, childAfter, rfl, rfl, rfl⟩
  · rintro (⟨childAfter, childResult, rfl⟩ | ⟨failure, childAfter, childResult, rfl, rfl⟩)
    · exact (isolateBlock_captured_success_trace capture childResult).1
    · exact (isolateBlock_captured_reject_trace capture childResult).1

/-- Every captured success restores the parent's complete source context and
resumes precisely after the closing brace, regardless of the child's cursor. -/
theorem isolateBlock_captured_success_frame
    {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body output) :
    output.file = input.file ∧ output.tokens = input.tokens ∧
      output.window = input.window ∧ output.cursor = captured.window.endIndex := by
  rcases (isolateBlock_captured_success_iff capture).mp result with
    ⟨childAfter, childResult, rfl⟩ | ⟨failure, childAfter, childResult, rfl, rfl⟩
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

/-- Forward diagnostic classification retains both branches' exact event order,
without claiming that either executable child outcome is an independent grammar. -/
theorem isolateBlock_captured_success_trace_cases
    {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body output) :
    (∃ childAfter,
      parser (input.enterWindow input.cursor captured.window) = .ok body childAfter ∧
      output.diagnostics = input.diagnostics ++ childAfter.diagnostics) ∨
    (∃ failure childAfter,
      parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter ∧
      body = { span := captured.span, value := [] } ∧
      output.diagnostics = input.diagnostics ++ childAfter.diagnostics ++ [failure.toDiagnostic]) := by
  rcases (isolateBlock_captured_success_iff capture).mp result with
    ⟨childAfter, childResult, rfl⟩ | ⟨failure, childAfter, childResult, rfl, rfl⟩
  · exact .inl ⟨childAfter, childResult, (isolateBlock_captured_success_trace capture childResult).2⟩
  · exact .inr ⟨failure, childAfter, childResult, rfl,
      (isolateBlock_captured_reject_trace capture childResult).2⟩

/-- Balanced isolation never returns an ordinary rejection to its parent. -/
theorem isolateBlock_captured_ne_reject
    {parser : Parser Block} {input rejected : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured) :
    isolateBlock parser input ≠ .reject failure rejected := by
  simp only [isolateBlock, capture]
  cases parser (input.enterWindow input.cursor captured.window) <;> simp

end Solcore.Syntax.Parser
