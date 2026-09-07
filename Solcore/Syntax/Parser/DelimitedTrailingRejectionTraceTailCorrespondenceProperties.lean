import Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceCompletenessProperties

/-! Exact rejection correspondences at the trailing-enabled tail-loop boundary.
Fuel and arbitrary reverse prefixes are explicit; the production wrappers use
the tail input's remaining count, independently of the full-list entry bound. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem afterDelimitedElement_trailing_production_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace
      elementRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace) :
    ∃ failure rejected, afterDelimitedElement element closing true context phase opening
        (input.remainingCount + 1) elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_trailing_trace_reject_complete successComplete rejectComplete contextFrame
    closing context phase opening (input.remainingCount + 1) elementsRev rejection (by omega)

theorem afterDelimitedElement_trailing_trace_reject_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) {input : State} (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, afterDelimitedElement element closing true context phase opening fuel elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = diagnostic ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact afterDelimitedElement_trailing_trace_reject_complete successComplete rejectComplete contextFrame
      closing context phase opening fuel elementsRev rejection adequate
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases afterDelimitedElement_trailing_reject_trace_sound successSound rejectSound contextFrame
        closing context phase opening fuel elementsRev input failure rejected result with
      ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

theorem afterDelimitedElement_trailing_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) {input : State} (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, afterDelimitedElement element closing true context phase opening fuel elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  rw [afterDelimitedElement_trailing_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame closing context phase opening fuel elementsRev adequate]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

theorem afterDelimitedElement_trailing_production_trace_reject_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, afterDelimitedElement element closing true context phase opening
        (input.remainingCount + 1) elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_trailing_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame closing context phase opening (input.remainingCount + 1) elementsRev (by omega)

theorem afterDelimitedElement_trailing_production_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, afterDelimitedElement element closing true context phase opening
        (input.remainingCount + 1) elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_trailing_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
    contextFrame closing context phase opening (input.remainingCount + 1) elementsRev (by omega)

end Solcore.Syntax.Parser
