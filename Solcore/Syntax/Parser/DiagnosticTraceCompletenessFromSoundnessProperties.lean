import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.DeclarativeTraceOutcomeSpec

/-! Exact trace functionality and ordinary execution turn both soundness
directions into completeness. The independent joint specification alone gives
no existence: the explicit no-invariant assumption excludes the third runtime
reply. No validity, source/window frame, or token-carrier law is imposed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {α : Type} {parser : Parser α}
  {traceParses : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop}
  {traceRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- At one input, soundness and absence of invariant failure realize every
successful trace with the same AST, remainder, and appended event sequence. -/
theorem trace_success_exists_ok_of_sound
    (successSound : ParserTraceSuccessSound parser traceParses)
    (rejectSound : ParserTraceRejectSound parser traceRejects)
    {input : State}
    (outcomes : TraceExactOutcomeSpec traceParses traceRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, parser input ≠ .invariant error)
    {value : α} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : traceParses input.file.id input.window.endByte input.declarativeRemainder value after trace) :
    ∃ output, parser input = .ok value output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace := by
  cases result : parser input with
  | ok actual output =>
      rcases successSound result with ⟨actualTrace, actualParsed, events⟩
      rcases outcomes.successResultUnique actualParsed parsed with ⟨rfl, afterEq, rfl⟩
      exact ⟨output, rfl, afterEq, events⟩
  | reject failure output =>
      rcases rejectSound result with ⟨actualTrace, rejected, _⟩
      exact False.elim (outcomes.successRejectDisjoint rejected ⟨value, after, trace, parsed⟩)
  | invariant error => exact False.elim (invariantFree error result)

/-- At one input, rejection completeness retains its exact terminal report
separately from the preceding event suffix; no report is added to that suffix. -/
theorem trace_reject_exists_reject_of_sound
    (successSound : ParserTraceSuccessSound parser traceParses)
    (rejectSound : ParserTraceRejectSound parser traceRejects)
    {input : State}
    (outcomes : TraceExactOutcomeSpec traceParses traceRejects input.file.id input.window.endByte)
    (invariantFree : ∀ error, parser input ≠ .invariant error)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : traceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure output, parser input = .reject failure output ∧ output.declarativeRemainder = after ∧
      failure.toDiagnostic = report ∧ output.diagnostics = input.diagnostics ++ trace := by
  cases result : parser input with
  | ok value output =>
      rcases successSound result with ⟨actualTrace, parsed, _⟩
      exact False.elim (outcomes.successRejectDisjoint rejection ⟨value, _, actualTrace, parsed⟩)
  | reject failure output =>
      rcases rejectSound result with ⟨actualTrace, actualRejected, events⟩
      rcases outcomes.rejectResultUnique actualRejected rejection with ⟨afterEq, reportEq, rfl⟩
      exact ⟨failure, output, rfl, afterEq, reportEq, events⟩
  | invariant error => exact False.elim (invariantFree error result)

/-- Global no-invariant execution supplies the unrestricted success contract,
including arbitrary incoming diagnostic accumulators. -/
theorem trace_success_complete_of_sound
    (successSound : ParserTraceSuccessSound parser traceParses)
    (rejectSound : ParserTraceRejectSound parser traceRejects)
    (outcomes : ∀ source endByte, TraceExactOutcomeSpec traceParses traceRejects source endByte)
    (invariantFree : ∀ input error, parser input ≠ .invariant error) :
    ParserTraceSuccessComplete parser traceParses := by
  intro input value after trace parsed
  exact trace_success_exists_ok_of_sound successSound rejectSound
    (outcomes input.file.id input.window.endByte) (invariantFree input) parsed

/-- Global no-invariant execution supplies the unrestricted rejection
contract, preserving the actual failure payload and exact ordered events. -/
theorem trace_reject_complete_of_sound
    (successSound : ParserTraceSuccessSound parser traceParses)
    (rejectSound : ParserTraceRejectSound parser traceRejects)
    (outcomes : ∀ source endByte, TraceExactOutcomeSpec traceParses traceRejects source endByte)
    (invariantFree : ∀ input error, parser input ≠ .invariant error) :
    ParserTraceRejectComplete parser traceRejects := by
  intro input after report trace rejection
  exact trace_reject_exists_reject_of_sound successSound rejectSound
    (outcomes input.file.id input.window.endByte) (invariantFree input) rejection

end Solcore.Syntax.Parser
