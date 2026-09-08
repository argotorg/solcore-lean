import Solcore.Syntax.DeclarativeExpressionPostfixTraceProperties
import Solcore.Syntax.Parser.ExpressionPostfixTraceSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties

/-! Pointwise correspondence for the actual production-fuel postfix parser.
Independent atom/nested exactness and observed soundness require a separate
actual no-invariant premise for completeness. Child completeness or context
alone cannot supply the production tail's remaining-count fuel adequacy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

variable {nested : Parser Expr} {block : Parser Block}
  {atomTrace nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {atomRejects nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (atomSound : ParserTraceSuccessSound (expressionAtom nested block) atomTrace)
  (atomRejectSound : ParserTraceRejectSound (expressionAtom nested block) atomRejects)
  (atomContext : ParserSuccessContext (expressionAtom nested block))
  (nestedSound : ParserTraceSuccessSound nested nestedTrace)
  (nestedRejectSound : ParserTraceRejectSound nested nestedRejects)
  (nestedContext : ParserSuccessContext nested) {input : State}
  (atoms : TraceExactOutcomeSpec atomTrace atomRejects input.file.id input.window.endByte)
  (nestedOutcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
  (invariantFree : ∀ error, expressionPostfix nested block input ≠ .invariant error)
  {value : Expr} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}

include atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree

theorem expressionPostfix_trace_success_complete_of_ne_invariant
    (parsed : ExpressionPostfixTraceParses atomTrace nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, expressionPostfix nested block input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  trace_success_exists_ok_of_sound
    (expressionPostfix_trace_success_sound atomSound atomContext nestedSound nestedContext)
    (expressionPostfix_reject_trace_sound atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext)
    (expressionPostfixTraceExactOutcomeSpec atoms nestedOutcomes) invariantFree parsed

theorem expressionPostfix_trace_reject_complete_of_ne_invariant
    (rejection : ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure rejected, expressionPostfix nested block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  trace_reject_exists_reject_of_sound
    (expressionPostfix_trace_success_sound atomSound atomContext nestedSound nestedContext)
    (expressionPostfix_reject_trace_sound atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext)
    (expressionPostfixTraceExactOutcomeSpec atoms nestedOutcomes) invariantFree rejection

theorem expressionPostfix_trace_success_iff_of_ne_invariant :
    ExpressionPostfixTraceParses atomTrace nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, expressionPostfix nested block input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionPostfix_trace_success_complete_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree
  · rintro ⟨output, result, afterEq, events⟩
    rcases expressionPostfix_trace_success_sound atomSound atomContext nestedSound nestedContext result with
      ⟨actualTrace, parsed, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, same] using parsed

theorem expressionPostfix_trace_reject_iff_of_ne_invariant :
    ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
    ∃ failure rejected, expressionPostfix nested block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact expressionPostfix_trace_reject_complete_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases expressionPostfix_reject_trace_sound atomSound atomRejectSound atomContext nestedSound
        nestedRejectSound nestedContext result with ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem expressionPostfix_trace_reject_failure_iff_of_ne_invariant {failure : Failure} :
    ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, expressionPostfix nested block input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [expressionPostfix_trace_reject_iff_of_ne_invariant atomSound atomRejectSound atomContext
    nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

end Solcore.Syntax.Parser
