import Solcore.Syntax.Parser.IsolatedBlockDiagnosticTraceProperties

/-! Consumers of executable isolation laws, preserving order and duplicates. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserIsolatedBlockDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @State.mergeDiagnostics_diagnostics_eq_append
example := @isolateBlock_captured_success_iff
example := @isolateBlock_captured_success_trace_cases
example := @isolateBlock_captured_ne_reject

example (input : State) (captured : BlockInternals.CapturedBlock) :
    (input.enterWindow input.cursor captured.window).diagnostics = [] ∧
      (input.enterWindow input.cursor captured.window).file = input.file ∧
      (input.enterWindow input.cursor captured.window).tokens = input.tokens ∧
      (input.enterWindow input.cursor captured.window).cursor = input.cursor ∧
      (input.enterWindow input.cursor captured.window).window = captured.window :=
  ⟨State.enterWindow_diagnostics_eq_nil _ _ _, rfl, rfl, rfl, rfl⟩

example {parser : Parser Block} {input rejected : State} {failure : Failure}
    (notCaptured : BlockInternals.captureBlock? input = none)
    (childResult : parser input = .reject failure rejected) :
    isolateBlock parser input = .reject failure rejected :=
  (isolateBlock_eq_of_no_capture parser notCaptured).trans childResult

example {parser : Parser Block} {input output : State} {body : Block}
    (notCaptured : BlockInternals.captureBlock? input = none)
    (childResult : parser input = .ok body output) :
    isolateBlock parser input = .ok body output :=
  (isolateBlock_eq_of_no_capture parser notCaptured).trans childResult

example {parser : Parser Block} {input childAfter : State} {body : Block}
    {captured : BlockInternals.CapturedBlock} {prior events : List ParseDiagnostic}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .ok body childAfter)
    (priorEq : input.diagnostics = prior) (eventsEq : childAfter.diagnostics = events) :
    ∃ output, isolateBlock parser input = .ok body output ∧
      output.diagnostics = prior ++ events := by
  have traced := isolateBlock_captured_success_trace capture childResult
  exact ⟨_, traced.1, by simpa only [priorEq, eventsEq] using traced.2⟩

example {parser : Parser Block} {input childAfter : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock} {prior events : List ParseDiagnostic}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter)
    (priorEq : input.diagnostics = prior) (eventsEq : childAfter.diagnostics = events) :
    ∃ output, isolateBlock parser input = .ok { span := captured.span, value := [] } output ∧
      output.diagnostics = prior ++ events ++ [failure.toDiagnostic] := by
  have traced := isolateBlock_captured_reject_trace capture childResult
  exact ⟨_, traced.1, by simpa only [priorEq, eventsEq] using traced.2⟩

example {parser : Parser Block} {input childAfter : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock} (prior event : ParseDiagnostic)
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter)
    (priorEq : input.diagnostics = [prior])
    (eventsEq : childAfter.diagnostics = [event, event]) :
    ∃ output, isolateBlock parser input = .ok { span := captured.span, value := [] } output ∧
      output.diagnostics = [prior, event, event, failure.toDiagnostic] := by
  have traced := isolateBlock_captured_reject_trace capture childResult
  exact ⟨_, traced.1, by simpa only [priorEq, eventsEq,
    List.cons_append, List.nil_append] using traced.2⟩

example {parser : Parser Block} {input childAfter : State} {failure : Failure}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .reject failure childAfter)
    (priorEq : input.diagnostics = [failure.toDiagnostic])
    (eventsEq : childAfter.diagnostics = [failure.toDiagnostic]) :
    ∃ output, isolateBlock parser input = .ok { span := captured.span, value := [] } output ∧
      output.diagnostics = [failure.toDiagnostic, failure.toDiagnostic, failure.toDiagnostic] := by
  have traced := isolateBlock_captured_reject_trace capture childResult
  exact ⟨_, traced.1, by simpa only [priorEq, eventsEq,
    List.cons_append, List.nil_append] using traced.2⟩

example {parser : Parser Block} {input : State} {error : ParserInvariantError}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (childResult : parser (input.enterWindow input.cursor captured.window) = .invariant error) :
    isolateBlock parser input = .invariant error :=
  (isolateBlock_captured_invariant_iff capture).mpr childResult

example {parser : Parser Block} {input : State} {error : ParserInvariantError}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .invariant error) :
    parser (input.enterWindow input.cursor captured.window) = .invariant error :=
  (isolateBlock_captured_invariant_iff capture).mp result

example {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body output) :
    output.file = input.file ∧ output.tokens = input.tokens ∧
      output.window = input.window ∧ output.cursor = captured.window.endIndex :=
  isolateBlock_captured_success_frame capture result

example {parser : Parser Block} {input output : State} {body : Block}
    {captured : BlockInternals.CapturedBlock} {nextToken : Token}
    (capture : BlockInternals.captureBlock? input = some captured)
    (result : isolateBlock parser input = .ok body output)
    (inside : captured.window.endIndex < input.window.endIndex)
    (following : input.tokens[captured.window.endIndex]? = some nextToken) :
    output.peek? = some nextToken := by
  rcases isolateBlock_captured_success_frame capture result with
    ⟨_, tokensEq, windowEq, cursorEq⟩
  simp only [State.peek?, tokensEq, windowEq, cursorEq, inside, if_true, following]

end Solcore.Test.SyntaxParserIsolatedBlockDiagnosticTraceProperties
