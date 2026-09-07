import Solcore.Syntax.Parser.ParenthesizedRejectionTraceCompletenessProperties

/-! Adequate raw-tail and production parenthesized correspondences preserve
the entire Failure, arbitrary incoming events, and reverse element prefixes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem tupleTail_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, tupleTail nested opening fuel elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact tupleTail_trace_reject_complete successComplete rejectComplete contextFrame
      opening fuel elementsRev rejection adequate
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases tupleTail_reject_trace_sound successSound rejectSound contextFrame opening fuel elementsRev input failure rejected result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem tupleTail_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, tupleTail nested opening fuel elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [tupleTail_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame opening fuel elementsRev adequate]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem parenthesized_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State}
    {after : DeclarativeGrammar.Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedExpressionTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, parenthesized nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parenthesized_trace_reject_complete successComplete rejectComplete contextFrame
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases parenthesized_reject_trace_sound successSound rejectSound contextFrame result with
      ⟨actualTrace, rejection, actualEvents⟩
    have same := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, same] using rejection

theorem parenthesized_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested)
    {input : State}
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedExpressionTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, parenthesized nested input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [parenthesized_trace_reject_iff successSound rejectSound successComplete rejectComplete contextFrame]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem tupleTail_production_trace_reject_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
    ∃ failure rejected, tupleTail nested opening (input.remainingCount + 1) elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = report ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame opening (input.remainingCount + 1) elementsRev (by omega)

theorem tupleTail_production_trace_reject_failure_iff
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (successComplete : ExpressionTraceSuccessComplete nested elementTrace)
    (rejectComplete : ExpressionTraceRejectComplete nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) (elementsRev : List Expr)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, tupleTail nested opening (input.remainingCount + 1) elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  tupleTail_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
    contextFrame opening (input.remainingCount + 1) elementsRev (by omega)

end Solcore.Syntax.Parser.ExpressionAtomInternals
