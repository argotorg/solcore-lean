import Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceSoundnessProperties

/-! Exact trailing-enabled rejection execution from independent derivations.
Strict child progress and the unchanged endIndex bound production fuel without
requiring valid input, immutable token carriers, or a rejected-state frame. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DelimitedTraceInternals

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- Adequate tail-loop fuel realizes the first rejecting derivation with any
reverse element prefix. No diagnostic is added for that prefix at rejection. -/
theorem afterDelimitedElement_trailing_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace
      elementRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace)
    (adequate : input.remainingCount < fuel) :
    ∃ failure rejected, afterDelimitedElement element closing true context phase opening fuel elementsRev input =
      .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = diagnostic ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing elementsRev input after diagnostic trace with
  | zero => omega
  | succ fuel ih =>
      cases rejection with
      | delimiterMissing commaAbsent closingAbsent reported =>
          rcases (rejectAt_reports_iff (alpha := DelimitedList α)).mp reported with ⟨failure, result, reportEq⟩
          exact ⟨failure, input, by
            simp only [afterDelimitedElement, symbol_absent .comma commaAbsent, Bool.false_eq_true,
              if_false, symbol_absent closing closingAbsent, result], rfl, reportEq, by simp⟩
      | elementRejected commaSpan commaParsed closingAbsent childRejected =>
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma context commaParsed
          have commaPresent := symbol_present .comma commaParsed
          rcases commaParsed with ⟨commaToken, rfl⟩
          have closingFalse := symbol_absent closing
            (input := { input with cursor := input.cursor + 1 }) closingAbsent
          rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) childRejected with
            ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
          exact ⟨failure, rejected, by
            simp only [afterDelimitedElement, commaPresent, if_true, commaResult,
              Bool.true_and, closingFalse, Bool.false_eq_true, if_false, result], afterEq, reportEq, diagnostics⟩
      | laterRejected commaSpan commaParsed closingAbsent childParsed progress tailRejected =>
          rename_i afterComma afterElement value childEvents tailEvents
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma context commaParsed
          have commaPresent := symbol_present .comma commaParsed
          rcases commaParsed with ⟨commaToken, rfl⟩
          have closingFalse := symbol_absent closing
            (input := { input with cursor := input.cursor + 1 }) closingAbsent
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) childParsed with
            ⟨next, childResult, nextAfter, childEq⟩
          have frame := contextFrame childResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← nextAfter, State.declarativeRemainder] using progress
          have tailAtNext : DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace
              elementRejects next.file.id next.window.endByte next.declarativeRemainder after diagnostic tailEvents := by
            simpa only [frame.1, frame.2, nextAfter] using tailRejected
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := commaToken.1
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih (value :: elementsRev) tailAtNext nextAdequate with
            ⟨failure, rejected, tailResult, afterEq, reportEq, diagnostics⟩
          refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
          · simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and, closingFalse,
              Bool.false_eq_true, if_false, childResult, nextProgress]
            exact tailResult
          · rw [diagnostics, childEq, List.append_assoc]
            rfl

/-- The production fuel is measured immediately after the opening delimiter,
not after the first child. Its adequacy follows from that child's strict progress. -/
theorem delimited_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserTraceRejectComplete (delimited opening closing allowEmpty element context phase)
      (DeclarativeGrammar.TrailingDelimitedListTraceRejects opening closing allowEmpty context
        elementTrace elementRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | openingMissing absent reported =>
      rcases (symbol_reject_reports_iff opening context).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [delimited, delimitedWithPolicy, result],
        rfl, reportEq, by simp⟩
  | firstRejected openingSpan openingParsed continues childRejected =>
      have openingResult := symbol_eq_ok_of_exactTokenParses opening context openingParsed
      rcases openingParsed with ⟨openingToken, rfl⟩
      have guard := guard_false_of_preferredCloseNotTaken closing allowEmpty
        (input := { input with cursor := input.cursor + 1 }) continues
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) childRejected with
        ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by
        simp only [delimited, delimitedWithPolicy, openingResult, guard,
          Bool.false_eq_true, if_false, result], afterEq, reportEq, diagnostics⟩
  | tailRejected openingSpan openingParsed continues childParsed progress tailRejected =>
      rename_i afterOpening afterFirst value childEvents tailEvents
      have openingResult := symbol_eq_ok_of_exactTokenParses opening context openingParsed
      rcases openingParsed with ⟨openingToken, rfl⟩
      have guard := guard_false_of_preferredCloseNotTaken closing allowEmpty
        (input := { input with cursor := input.cursor + 1 }) continues
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) childParsed with
        ⟨next, childResult, nextAfter, childEq⟩
      have frame := contextFrame childResult
      have nextProgress : input.cursor + 1 < next.cursor := by
        simpa only [← nextAfter, State.declarativeRemainder] using progress
      have tailAtNext : DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace
          elementRejects next.file.id next.window.endByte next.declarativeRemainder after diagnostic tailEvents := by
        simpa only [frame.1, frame.2, nextAfter] using tailRejected
      have adequate : next.remainingCount <
          ({ input with cursor := input.cursor + 1 } : State).remainingCount + 1 := by
        simp only [State.remainingCount, frame.2]
        omega
      rcases afterDelimitedElement_trailing_trace_reject_complete successComplete rejectComplete contextFrame
          closing context phase { span := openingSpan, value := .symbol opening }
          (({ input with cursor := input.cursor + 1 } : State).remainingCount + 1) [value]
          tailAtNext adequate with ⟨failure, rejected, tailResult, afterEq, reportEq, diagnostics⟩
      refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
      · simp only [delimited, delimitedWithPolicy, openingResult, guard, Bool.false_eq_true,
          if_false, childResult, nextProgress, if_true]
        exact tailResult
      · rw [diagnostics, childEq, List.append_assoc]
        rfl

end Solcore.Syntax.Parser
