import Solcore.Syntax.Parser.ExpressionPostfixTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ExpressionPostfixTraceContextProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! Whole-State correspondence for actual atom-plus-postfix execution at an
explicit invariant-free input. Rejected child frames preserve only file and
endByte; the exact remainder retains replacement tokens and numeric endIndex.
No child progress, validity, or hidden production-fuel completeness is assumed. -/

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

include atomSound atomRejectSound atomContext nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree

theorem expressionPostfix_trace_success_state_iff_of_ne_invariant
    {value : Expr} {after : Remainder} {trace : List ParseDiagnostic} :
    ExpressionPostfixTraceParses atomTrace nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      expressionPostfix nested block input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases (expressionPostfix_trace_success_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mp parsed with
        ⟨output, result, afterEq, events⟩
    have frame := expressionPostfix_trace_success_context atomContext nestedContext result
    have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact (expressionPostfix_trace_success_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionPostfix_trace_reject_failure_state_iff_of_ne_invariant
    (atomRejectFrame : ∀ {input rejected failure}, expressionAtom nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
      expressionPostfix nested block input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases (expressionPostfix_trace_reject_failure_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mp rejection with
        ⟨rejected, result, afterEq, events⟩
    have frame := expressionPostfix_reject_context_of_windowProjection (view := TokenWindow.endByte)
      atomContext nestedContext atomRejectFrame nestedRejectFrame result
    have same := State.eq_traceResult_of_fields frame.1 frame.2 afterEq events
    exact same ▸ result
  · intro result
    exact (expressionPostfix_trace_reject_failure_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mpr
        ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem expressionPostfix_trace_reject_state_iff_of_ne_invariant
    (atomRejectFrame : ∀ {input rejected failure}, expressionAtom nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    (nestedRejectFrame : ∀ {input rejected failure}, nested input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ExpressionPostfixTraceRejects atomTrace nestedTrace atomRejects nestedRejects
      input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, expressionPostfix nested block input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases (expressionPostfix_trace_reject_iff_of_ne_invariant atomSound atomRejectSound atomContext
      nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree).mp rejection with
        ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (expressionPostfix_trace_reject_failure_state_iff_of_ne_invariant atomSound atomRejectSound
      atomContext nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree
      atomRejectFrame nestedRejectFrame).mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (expressionPostfix_trace_reject_failure_state_iff_of_ne_invariant atomSound atomRejectSound
      atomContext nestedSound nestedRejectSound nestedContext atoms nestedOutcomes invariantFree
      atomRejectFrame nestedRejectFrame).mpr result

end Solcore.Syntax.Parser
