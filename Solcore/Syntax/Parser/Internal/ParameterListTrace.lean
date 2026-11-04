import Solcore.Syntax.Internal.ParameterTrace
import Solcore.Syntax.Parser.Internal.ParameterTrace
import Solcore.Syntax.Parser.Internal.ParameterTotality
import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.ParameterSoundness
import Solcore.Syntax.Parser.Expression.Atom

/-!
Parser side of the parameter-list traces: function and inline lambda
parameter lists inherit unconditional exact traces from their elements.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParametersTraceProperties
/-! Exact traces for the actual functionParameters list, including recovery
inside its public namedParameter children. Every input State is supported.
No signature parsing or unconditional cascade protection is claimed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem functionParameters_trace_success_sound :
    ParserTraceSuccessSound functionParameters FunctionParametersTraceParses :=
  delimited_trace_success_sound namedParameter_trace_success_sound namedParameter_success_context
    .leftParen .rightParen true .parameter .topLevel

theorem functionParameters_reject_trace_sound :
    ParserTraceRejectSound functionParameters FunctionParametersTraceRejects :=
  delimited_reject_trace_sound namedParameter_trace_success_sound namedParameter_reject_trace_sound
    namedParameter_success_context .leftParen .rightParen true .parameter .topLevel

theorem functionParameters_trace_success_complete :
    ParserTraceSuccessComplete functionParameters FunctionParametersTraceParses :=
  delimited_trace_success_complete namedParameter_trace_success_complete namedParameter_success_context
    .leftParen .rightParen true .parameter .topLevel

theorem functionParameters_trace_reject_complete :
    ParserTraceRejectComplete functionParameters FunctionParametersTraceRejects :=
  delimited_trace_reject_complete namedParameter_trace_success_complete namedParameter_trace_reject_complete
    namedParameter_success_context .leftParen .rightParen true .parameter .topLevel

theorem functionParameters_success_context : ParserSuccessContext functionParameters :=
  delimited_success_context namedParameter_success_context .leftParen .rightParen true .parameter .topLevel

theorem functionParameters_reject_context {input rejected : State} {failure : Failure}
    (result : functionParameters input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := delimited_preservesTokenWindow .leftParen .rightParen true namedParameter
    .parameter .topLevel namedParameter_preservesTokenWindow input
  change (functionParameters input).PreservesTokenWindow input at window
  rw [result] at window
  exact ⟨(delimited_preservesFile .leftParen .rightParen true namedParameter .parameter .topLevel
    namedParameter_preservesFile).file_eq_of_reject result, window.2⟩

private theorem child_unrestricted_contract (fuel : Nat) :
    UnrestrictedFuelElementContract namedParameter fuel where
  endIndexOnSuccess result := congrArg TokenWindow.endIndex (namedParameter_success_context result).2
  cursorLtOnSuccess := namedParameter_cursor_lt_onSuccess
  ordinary input _ := namedParameter_ordinary_unrestricted input

theorem functionParameters_ordinary_unrestricted : Parser.Ordinary functionParameters := by
  intro input
  exact delimited_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true namedParameter
    .parameter .topLevel input.remainingCount (child_unrestricted_contract _) input (by omega)

theorem functionParameters_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    functionParameters input ≠ .invariant error :=
  functionParameters_ordinary_unrestricted.ne_invariant input error

theorem functionParameters_trace_success_iff
    {input : State} {value : DelimitedList FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    FunctionParametersTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, functionParameters input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact functionParameters_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases functionParameters_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem functionParameters_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    FunctionParametersTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, functionParameters input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact functionParameters_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases functionParameters_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem functionParameters_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    FunctionParametersTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, functionParameters input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [functionParameters_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem functionParameters_trace_success_state_iff
    {input : State} {value : DelimitedList FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    FunctionParametersTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      functionParameters input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases functionParameters_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := functionParameters_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact functionParameters_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem functionParameters_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    FunctionParametersTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      functionParameters input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases functionParameters_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := functionParameters_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact functionParameters_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem functionParameters_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    FunctionParametersTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, functionParameters input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases functionParameters_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, functionParameters_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ functionParameters_trace_reject_failure_state_iff.mpr result

/-! Non-vacuous existence follows from unrestricted ordinary execution and
soundness, not from the independent joint uniqueness/disjointness laws. -/

theorem functionParameters_exists_trace_outcome (input : State) :
    (∃ value output trace,
      functionParameters input = .ok value output ∧
      FunctionParametersTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      functionParameters input = .reject failure rejected ∧
      FunctionParametersTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases functionParameters_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases functionParameters_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases functionParameters_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem functionParametersTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, FunctionParametersTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, FunctionParametersTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases functionParameters_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParametersTraceProperties
/-! Exact traces for the inline parenthesized lambda-parameter list used by
lambdaExpression. Its expression phase and public recovering children are
unchanged. These laws cover only the list, not the lambda return type or body.
No executable wrapper or unconditional cascade protection is introduced. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem lambdaParameters_trace_success_sound :
    ParserTraceSuccessSound (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) LambdaParametersTraceParses :=
  delimited_trace_success_sound lambdaParameter_trace_success_sound lambdaParameter_success_context
    .leftParen .rightParen true .parameter .expression

theorem lambdaParameters_reject_trace_sound :
    ParserTraceRejectSound (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) LambdaParametersTraceRejects :=
  delimited_reject_trace_sound lambdaParameter_trace_success_sound lambdaParameter_reject_trace_sound
    lambdaParameter_success_context .leftParen .rightParen true .parameter .expression

theorem lambdaParameters_trace_success_complete :
    ParserTraceSuccessComplete (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) LambdaParametersTraceParses :=
  delimited_trace_success_complete lambdaParameter_trace_success_complete lambdaParameter_success_context
    .leftParen .rightParen true .parameter .expression

theorem lambdaParameters_trace_reject_complete :
    ParserTraceRejectComplete (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) LambdaParametersTraceRejects :=
  delimited_trace_reject_complete lambdaParameter_trace_success_complete lambdaParameter_trace_reject_complete
    lambdaParameter_success_context .leftParen .rightParen true .parameter .expression

theorem lambdaParameters_success_context : ParserSuccessContext (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) :=
  delimited_success_context lambdaParameter_success_context .leftParen .rightParen true .parameter .expression

theorem lambdaParameters_reject_context {input rejected : State} {failure : Failure}
    (result : (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := delimited_preservesTokenWindow .leftParen .rightParen true lambdaParameter
    .parameter .expression lambdaParameter_preservesTokenWindow input
  change ((delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input).PreservesTokenWindow input at window
  rw [result] at window
  exact ⟨(delimited_preservesFile .leftParen .rightParen true lambdaParameter .parameter .expression
    lambdaParameter_preservesFile).file_eq_of_reject result, window.2⟩

private theorem lambdaParameter_child_unrestricted_contract (fuel : Nat) :
    UnrestrictedFuelElementContract lambdaParameter fuel where
  endIndexOnSuccess result := congrArg TokenWindow.endIndex (lambdaParameter_success_context result).2
  cursorLtOnSuccess := lambdaParameter_cursor_lt_onSuccess
  ordinary input _ := lambdaParameter_ordinary_unrestricted input

theorem lambdaParameters_ordinary_unrestricted : Parser.Ordinary (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) := by
  intro input
  exact delimited_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true lambdaParameter
    .parameter .expression input.remainingCount (lambdaParameter_child_unrestricted_contract _) input (by omega)

theorem lambdaParameters_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input ≠ .invariant error :=
  lambdaParameters_ordinary_unrestricted.ne_invariant input error

theorem lambdaParameters_trace_success_iff
    {input : State} {value : DelimitedList LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParametersTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaParameters_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases lambdaParameters_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem lambdaParameters_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaParametersTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaParameters_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases lambdaParameters_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem lambdaParameters_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaParametersTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [lambdaParameters_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem lambdaParameters_trace_success_state_iff
    {input : State} {value : DelimitedList LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParametersTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases lambdaParameters_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := lambdaParameters_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact lambdaParameters_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem lambdaParameters_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaParametersTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases lambdaParameters_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := lambdaParameters_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact lambdaParameters_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem lambdaParameters_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaParametersTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases lambdaParameters_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, lambdaParameters_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ lambdaParameters_trace_reject_failure_state_iff.mpr result

/-! Non-vacuous existence follows from unrestricted ordinary execution and
soundness, not from the independent joint uniqueness/disjointness laws. -/

theorem lambdaParameters_exists_trace_outcome (input : State) :
    (∃ value output trace,
      (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .ok value output ∧
      LambdaParametersTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) input = .reject failure rejected ∧
      LambdaParametersTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases lambdaParameters_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases lambdaParameters_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases lambdaParameters_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem lambdaParametersTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, LambdaParametersTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, LambdaParametersTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases lambdaParameters_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser
end
