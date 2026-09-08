import Solcore.Syntax.DeclarativePostfixTailRejectionTraceProperties
import Solcore.Syntax.Parser.PostfixTailSuccessTraceSoundnessProperties
import Solcore.Syntax.Parser.PostfixTailRejectionTraceSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties

/-! Pointwise postfix correspondence separates deterministic independent
outcomes from actual invariant exclusion. No fuel bound, child progress,
rejected carrier frame, or unconditional existence is hidden in these laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound nested nestedTrace)
  (rejectSound : ParserTraceRejectSound nested nestedRejects)
  (contextFrame : ParserSuccessContext nested) (block : Parser Block) (fuel : Nat) (base : Expr)
  {input : State}
  (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
  (invariantFree : ∀ error, postfixTail nested block fuel base input ≠ .invariant error)
  {value : Expr} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}

include successSound rejectSound contextFrame outcomes invariantFree

theorem postfixTail_trace_success_complete_of_ne_invariant
    (parsed : PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace) :
    ∃ output, postfixTail nested block fuel base input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  trace_success_exists_ok_of_sound
    (parser := postfixTail nested block fuel base)
    (fun result => postfixTail_trace_success_sound successSound contextFrame block fuel base _ _ _ result)
    (fun result => postfixTail_reject_trace_sound successSound rejectSound contextFrame block fuel base _ _ _ result)
    (postfixTailTraceExactOutcomeSpec outcomes base) invariantFree parsed

theorem postfixTail_trace_reject_complete_of_ne_invariant
    (rejection : PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace) :
    ∃ failure rejected, postfixTail nested block fuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  trace_reject_exists_reject_of_sound
    (parser := postfixTail nested block fuel base)
    (fun result => postfixTail_trace_success_sound successSound contextFrame block fuel base _ _ _ result)
    (fun result => postfixTail_reject_trace_sound successSound rejectSound contextFrame block fuel base _ _ _ result)
    (postfixTailTraceExactOutcomeSpec outcomes base) invariantFree rejection

theorem postfixTail_trace_success_iff_of_ne_invariant :
    PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace ↔
    ∃ output, postfixTail nested block fuel base input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact postfixTail_trace_success_complete_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree
  · rintro ⟨output, result, afterEq, events⟩
    rcases postfixTail_trace_success_sound successSound contextFrame block fuel base _ _ _ result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem postfixTail_trace_reject_iff_of_ne_invariant :
    PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace ↔
    ∃ failure rejected, postfixTail nested block fuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact postfixTail_trace_reject_complete_of_ne_invariant successSound rejectSound contextFrame
      block fuel base outcomes invariantFree
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases postfixTail_reject_trace_sound successSound rejectSound contextFrame block fuel base _ _ _ result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem postfixTail_trace_reject_failure_iff_of_ne_invariant {failure : Failure} :
    PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after failure.toDiagnostic trace ↔
    ∃ rejected, postfixTail nested block fuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [postfixTail_trace_reject_iff_of_ne_invariant successSound rejectSound contextFrame
    block fuel base outcomes invariantFree]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
