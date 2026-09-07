import Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceCompletenessProperties

/-! Exact trailing-enabled rejection iff theorems retain the complete uncommitted
failure and ordered appended diagnostics, including arbitrary incoming events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem delimited_trace_reject_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace
      elementRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, delimited opening closing allowEmpty element context phase input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = diagnostic ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact delimited_trace_reject_complete successComplete rejectComplete contextFrame
      opening closing allowEmpty context phase
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases delimited_reject_trace_sound successSound rejectSound contextFrame
        opening closing allowEmpty context phase result with ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

theorem delimited_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace
      elementRejects input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, delimited opening closing allowEmpty element context phase input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  rw [delimited_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame opening closing allowEmpty context phase]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

end Solcore.Syntax.Parser
