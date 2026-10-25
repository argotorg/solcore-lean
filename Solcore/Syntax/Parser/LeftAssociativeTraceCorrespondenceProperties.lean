import Solcore.Syntax.DeclarativeLeftAssociativeTraceProperties
import Solcore.Syntax.Parser.LeftAssociativeTraceSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties

/-! Whole left-associative correspondence uses independent operand exactness
and explicit pointwise invariant exclusion. Successful operand framing keeps
only file/endByte. Neither child completeness nor a full-window/progress law
is required, and independent uniqueness is not promoted to runtime totality. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

open DeclarativeGrammar

variable {operand : Parser Expr}
  {operandTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {operandRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound operand operandTrace)
  (rejectSound : ParserTraceRejectSound operand operandRejects)
  (successFrame : ∀ {input output value}, operand input = .ok value output →
    output.file = input.file ∧ output.window.endByte = input.window.endByte)
  (precedence : Nat) {input : State}
  (outcomes : TraceExactOutcomeSpec operandTrace operandRejects input.file.id input.window.endByte)
  (invariantFree : ∀ error, leftAssociative operand precedence input ≠ .invariant error)
  {value : Expr} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}

include successSound rejectSound successFrame outcomes invariantFree

theorem leftAssociative_trace_success_complete_of_ne_invariant
    (parsed : LeftAssociativeTraceParses operandTrace precedence input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, leftAssociative operand precedence input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  trace_success_exists_ok_of_sound
    (leftAssociative_trace_success_sound successSound successFrame precedence)
    (leftAssociative_reject_trace_sound successSound rejectSound successFrame precedence)
    (leftAssociativeTraceExactOutcomeSpec outcomes precedence) invariantFree parsed

theorem leftAssociative_trace_reject_complete_of_ne_invariant
    (rejection : LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after report trace) :
    ∃ failure rejected, leftAssociative operand precedence input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  trace_reject_exists_reject_of_sound
    (leftAssociative_trace_success_sound successSound successFrame precedence)
    (leftAssociative_reject_trace_sound successSound rejectSound successFrame precedence)
    (leftAssociativeTraceExactOutcomeSpec outcomes precedence) invariantFree rejection

theorem leftAssociative_trace_success_iff_of_ne_invariant :
    LeftAssociativeTraceParses operandTrace precedence input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, leftAssociative operand precedence input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact leftAssociative_trace_success_complete_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree
  · rintro ⟨output, result, afterEq, events⟩
    rcases leftAssociative_trace_success_sound successSound successFrame precedence result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem leftAssociative_trace_reject_iff_of_ne_invariant :
    LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, leftAssociative operand precedence input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact leftAssociative_trace_reject_complete_of_ne_invariant successSound rejectSound successFrame
      precedence outcomes invariantFree
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases leftAssociative_reject_trace_sound successSound rejectSound successFrame precedence result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem leftAssociative_trace_reject_failure_iff_of_ne_invariant {failure : Failure} :
    LeftAssociativeTraceRejects operandTrace operandRejects precedence input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, leftAssociative operand precedence input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [leftAssociative_trace_reject_iff_of_ne_invariant successSound rejectSound successFrame precedence outcomes invariantFree]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionInternals
