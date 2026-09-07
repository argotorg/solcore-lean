import Solcore.Syntax.DeclarativeTypeExprTraceOutcomeProperties
import Solcore.Syntax.Parser.TypeExprTraceSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties

/-! Recursive trace completeness at inputs where invariant failure is excluded.
The production parser's existing totality theorem supplies that premise on
valid states only. No unrestricted completeness or existence claim is hidden
in these pointwise correspondences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {input : State} {value : TypeExpr} {after : Remainder}
  {report : ParseDiagnostic} {trace : List ParseDiagnostic}

theorem typeExpr_trace_success_complete_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error)
    (parsed : TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace :=
  trace_success_exists_ok_of_sound typeExpr_trace_success_sound typeExpr_reject_trace_sound
    typeExprTraceExactOutcomeSpec invariantFree parsed

theorem typeExpr_trace_reject_complete_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error)
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace) :
    ∃ failure rejected, typeExpr input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  trace_reject_exists_reject_of_sound typeExpr_trace_success_sound typeExpr_reject_trace_sound
    typeExprTraceExactOutcomeSpec invariantFree rejection

theorem typeExpr_trace_success_iff_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error) :
    TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact typeExpr_trace_success_complete_of_ne_invariant invariantFree
  · rintro ⟨output, result, afterEq, events⟩
    rcases typeExpr_trace_success_sound result with ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem typeExpr_trace_reject_iff_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error) :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact typeExpr_trace_reject_complete_of_ne_invariant invariantFree
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases typeExpr_reject_trace_sound result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem typeExpr_trace_reject_failure_iff_of_ne_invariant
    (invariantFree : ∀ error, typeExpr input ≠ .invariant error) {failure : Failure} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [typeExpr_trace_reject_iff_of_ne_invariant invariantFree]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem typeExpr_trace_success_complete_onValid (inputValid : input.ValidFor)
    (parsed : TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_success_complete_of_ne_invariant (typeExpr_ne_invariant input inputValid) parsed

theorem typeExpr_trace_reject_complete_onValid (inputValid : input.ValidFor)
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace) :
    ∃ failure rejected, typeExpr input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_complete_of_ne_invariant (typeExpr_ne_invariant input inputValid) rejection

theorem typeExpr_trace_success_iff_onValid (inputValid : input.ValidFor) :
    TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_success_iff_of_ne_invariant (typeExpr_ne_invariant input inputValid)

theorem typeExpr_trace_reject_iff_onValid (inputValid : input.ValidFor) :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_iff_of_ne_invariant (typeExpr_ne_invariant input inputValid)

theorem typeExpr_trace_reject_failure_iff_onValid (inputValid : input.ValidFor) {failure : Failure} :
    TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, typeExpr input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  typeExpr_trace_reject_failure_iff_of_ne_invariant (typeExpr_ne_invariant input inputValid)

end Solcore.Syntax.Parser
