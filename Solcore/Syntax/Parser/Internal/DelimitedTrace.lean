import Solcore.Syntax.Internal.DelimitedTrace
import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-!
Parser side of the delimited-list traces: the executable list parsers
produce exactly the events of the trace grammar, on success and on rejection.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedClosingTraceProperties
/-! Silent exact closing and the two guards used by delimited trace proofs. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace DelimitedTraceInternals

theorem symbol_present (value : Symbol) {input : State} {span : SourceSpan}
    {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.symbol value)
      input.declarativeRemainder span after) : isSymbol input value = true := by
  have token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := parsed.1
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

theorem symbol_absent (value : Symbol) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol value)) : isSymbol input value = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases symbol_eq_ok_of_isSymbol_eq_true value .expression present with ⟨token, result⟩
  exact absent ⟨token.span, (symbol_ok_tokenAt value .expression result).1⟩

theorem preferredCloseNotTaken_of_guard_false (closing : Symbol) (allowClose : Bool)
    {input : State} (guard : (allowClose && isSymbol input closing) = false) :
    DeclarativeGrammar.PreferredCloseNotTaken closing allowClose input.declarativeRemainder := by
  cases allowClose with
  | false => exact .disabled
  | true => exact .absent (symbolAbsentAt_of_isSymbol_eq_false closing (by simpa using guard))

theorem guard_false_of_preferredCloseNotTaken (closing : Symbol) (allowClose : Bool)
    {input : State}
    (continues : DeclarativeGrammar.PreferredCloseNotTaken closing allowClose
      input.declarativeRemainder) : (allowClose && isSymbol input closing) = false := by
  cases continues with
  | disabled => rfl
  | absent absent => simpa only [Bool.true_and] using symbol_absent closing absent

end DelimitedTraceInternals

theorem closeDelimited_success_trace_sound {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α)
    {input output : State} {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input = .ok values output) :
    ∃ closingSpan,
      DeclarativeGrammar.ExactTokenParses (.symbol closing) input.declarativeRemainder
        closingSpan output.declarativeRemainder ∧
      values = { span := SourceSpan.cover opening.span closingSpan, elements := elementsRev.reverse } ∧
      output = { input with cursor := input.cursor + 1 } := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token next =>
      simp only [closingResult] at result
      cases result
      exact ⟨token.span, symbol_success_exactTokenParses closing context closingResult,
        rfl, (symbol_ok_tokenAt closing context closingResult).2⟩

theorem closeDelimited_trace_success_iff {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α)
    {input : State} {values : DelimitedList α} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    ((∃ closingSpan, DeclarativeGrammar.ExactTokenParses (.symbol closing)
      input.declarativeRemainder closingSpan after ∧
      values = { span := SourceSpan.cover opening.span closingSpan, elements := elementsRev.reverse }) ∧
      trace = []) ↔
    ∃ output, closeDelimited opening closing context elementsRev input = .ok values output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨⟨closingSpan, parsed, rfl⟩, rfl⟩
    have result := symbol_eq_ok_of_exactTokenParses closing context parsed
    refine ⟨{ input with cursor := input.cursor + 1 },
      by simp only [closeDelimited, result], parsed.2.symm, ?_⟩
    simp only [State.diagnostics, List.append_nil]
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
      ⟨closingSpan, parsed, valuesEq, stateEq⟩
    refine ⟨⟨closingSpan, afterEq ▸ parsed, valuesEq⟩, ?_⟩
    rw [stateEq] at diagnostics
    have : input.diagnostics ++ [] = input.diagnostics ++ trace := by
      simpa only [State.diagnostics, List.append_nil] using diagnostics
    exact (List.append_cancel_left this).symm

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceSoundnessProperties
/-! Exact no-trailing rejection reflection. Earlier child diagnostics survive
in order and the final report remains uncommitted. Successful source/window
preservation is explicit; no token-carrier or rejected-state frame is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DelimitedTraceInternals

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- Every fixed-fuel tail rejection reflects its exact report and event suffix,
independently of the arbitrary already-accumulated reverse element prefix. -/
theorem afterDelimitedElement_noTrailing_reject_trace_sound
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input failure rejected,
      afterDelimitedElement element closing false context phase opening fuel elementsRev input =
        .reject failure rejected →
      ∃ trace, DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace
        elementRejects input.file.id input.window.endByte input.declarativeRemainder
          rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input failure rejected result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input failure rejected result
      unfold afterDelimitedElement at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma context commaPresent with ⟨comma, commaResult⟩
        have commaParsed := symbol_success_exactTokenParses .comma context commaResult
        simp only [commaPresent, if_true, commaResult, Bool.false_and, Bool.false_eq_true, if_false] at result
        cases childResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            rcases rejectSound childResult with ⟨trace, childRejected, diagnostics⟩
            exact ⟨trace, .elementRejected comma.span commaParsed childRejected, diagnostics⟩
        | ok value next =>
            simp only [childResult] at result
            by_cases progress : next.cursor > input.cursor + 1
            · simp only [progress, if_true] at result
              rcases ih (value :: elementsRev) next failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
              rcases successSound childResult with ⟨childEvents, childParsed, childEq⟩
              have frame := contextFrame childResult
              have tailAtInput : DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context
                  elementTrace elementRejects input.file.id input.window.endByte next.declarativeRemainder
                  rejected.declarativeRemainder failure.toDiagnostic tailEvents := by
                simpa only [frame.1, frame.2] using tailRejected
              refine ⟨childEvents ++ tailEvents,
                .laterRejected comma.span commaParsed childParsed progress tailAtInput, ?_⟩
              rw [tailEq, childEq, List.append_assoc]
              rfl
            · simp only [progress, if_false] at result
              contradiction
      · have commaFalse := Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        by_cases closingPresent : isSymbol input closing = true
        · rcases symbol_eq_ok_of_isSymbol_eq_true closing context closingPresent with ⟨token, parsed⟩
          simp [closingPresent, closeDelimited, parsed] at result
        · have closingFalse := Bool.eq_false_iff.mpr closingPresent
          simp only [closingFalse, Bool.false_eq_true, if_false] at result
          have reported := rejectAt_reject_reports { head := .symbol .comma, tail := [.symbol closing] }
            context result
          unfold rejectAt at result
          cases result
          exact ⟨[], .delimiterMissing (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse)
            (symbolAbsentAt_of_isSymbol_eq_false closing closingFalse) reported.1, by simp⟩

/-- Complete list reflection retains opening/first-child/tail first-failure
priority under either empty policy, with arbitrary incoming diagnostics. -/
theorem delimitedNoTrailing_reject_trace_sound
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserTraceRejectSound (delimitedNoTrailing opening closing allowEmpty element context phase)
      (DeclarativeGrammar.NoTrailingDelimitedListTraceRejects opening closing allowEmpty context
        elementTrace elementRejects) := by
  intro input rejected failure result
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have shape := symbol_reject_state_eq opening context openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      have reported := (symbol_reject_reports_iff opening context).mpr ⟨failure, openingResult, rfl⟩
      exact ⟨[], .openingMissing reported.1 reported.2, by simp⟩
  | ok openingToken afterOpening =>
      have openingParsed := symbol_success_exactTokenParses opening context openingResult
      have shape := (symbol_ok_tokenAt opening context openingResult).2
      simp only [openingResult] at result
      by_cases emptyClose : (allowEmpty && isSymbol afterOpening closing) = true
      · have closingPresent : isSymbol afterOpening closing = true := by
          cases allowEmpty with
          | false => simp at emptyClose
          | true => simpa using emptyClose
        rcases symbol_eq_ok_of_isSymbol_eq_true closing context closingPresent with ⟨token, parsed⟩
        simp [emptyClose, closeDelimited, parsed] at result
      · have emptyFalse := Bool.eq_false_iff.mpr emptyClose
        have continues := preferredCloseNotTaken_of_guard_false closing allowEmpty emptyFalse
        simp only [emptyFalse, Bool.false_eq_true, if_false] at result
        cases childResult : element afterOpening with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            rcases rejectSound childResult with ⟨trace, childRejected, diagnostics⟩
            refine ⟨trace, .firstRejected openingToken.span openingParsed continues ?_, ?_⟩
            · simpa only [shape] using childRejected
            · simpa only [shape, State.diagnostics] using diagnostics
        | ok value next =>
            simp only [childResult] at result
            by_cases progress : next.cursor > afterOpening.cursor
            · simp only [progress, if_true] at result
              rcases afterDelimitedElement_noTrailing_reject_trace_sound successSound rejectSound contextFrame
                  closing context phase openingToken (afterOpening.remainingCount + 1) [value] next
                  failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
              rcases successSound childResult with ⟨childEvents, childParsed, childEq⟩
              have frame := contextFrame childResult
              have childAtInput : elementTrace input.file.id input.window.endByte afterOpening.declarativeRemainder
                  value next.declarativeRemainder childEvents := by simpa only [shape] using childParsed
              have tailAtInput : DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context
                  elementTrace elementRejects input.file.id input.window.endByte next.declarativeRemainder
                  rejected.declarativeRemainder failure.toDiagnostic tailEvents := by
                simpa only [frame.1, frame.2, shape] using tailRejected
              refine ⟨childEvents ++ tailEvents,
                .tailRejected openingToken.span openingParsed continues childAtInput progress tailAtInput, ?_⟩
              rw [tailEq, childEq, List.append_assoc]
              simp only [shape, State.diagnostics]
            · simp only [progress, if_false] at result
              contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceCompletenessProperties
/-! Exact no-trailing rejection execution from independent derivations.
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
theorem afterDelimitedElement_noTrailing_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace
      elementRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace)
    (adequate : input.remainingCount < fuel) :
    ∃ failure rejected, afterDelimitedElement element closing false context phase opening fuel elementsRev input =
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
      | elementRejected commaSpan commaParsed childRejected =>
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma context commaParsed
          have commaPresent := symbol_present .comma commaParsed
          rcases commaParsed with ⟨commaToken, rfl⟩
          rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) childRejected with
            ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
          exact ⟨failure, rejected, by
            simp only [afterDelimitedElement, commaPresent, if_true, commaResult,
              Bool.false_and, Bool.false_eq_true, if_false, result], afterEq, reportEq, diagnostics⟩
      | laterRejected commaSpan commaParsed childParsed progress tailRejected =>
          rename_i afterComma afterElement value childEvents tailEvents
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma context commaParsed
          have commaPresent := symbol_present .comma commaParsed
          rcases commaParsed with ⟨commaToken, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) childParsed with
            ⟨next, childResult, nextAfter, childEq⟩
          have frame := contextFrame childResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← nextAfter, State.declarativeRemainder] using progress
          have tailAtNext : DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace
              elementRejects next.file.id next.window.endByte next.declarativeRemainder after diagnostic tailEvents := by
            simpa only [frame.1, frame.2, nextAfter] using tailRejected
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := commaToken.1
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          rcases ih (value :: elementsRev) tailAtNext nextAdequate with
            ⟨failure, rejected, tailResult, afterEq, reportEq, diagnostics⟩
          refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
          · simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.false_and,
              Bool.false_eq_true, if_false, childResult, nextProgress]
            exact tailResult
          · rw [diagnostics, childEq, List.append_assoc]
            rfl

/-- The production fuel is measured immediately after the opening delimiter,
not after the first child. Its adequacy follows from that child's strict progress. -/
theorem delimitedNoTrailing_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserTraceRejectComplete (delimitedNoTrailing opening closing allowEmpty element context phase)
      (DeclarativeGrammar.NoTrailingDelimitedListTraceRejects opening closing allowEmpty context
        elementTrace elementRejects) := by
  intro input after diagnostic trace rejection
  cases rejection with
  | openingMissing absent reported =>
      rcases (symbol_reject_reports_iff opening context).mp ⟨absent, reported⟩ with ⟨failure, result, reportEq⟩
      exact ⟨failure, input, by simp only [delimitedNoTrailing, delimitedWithPolicy, result],
        rfl, reportEq, by simp⟩
  | firstRejected openingSpan openingParsed continues childRejected =>
      have openingResult := symbol_eq_ok_of_exactTokenParses opening context openingParsed
      rcases openingParsed with ⟨openingToken, rfl⟩
      have guard := guard_false_of_preferredCloseNotTaken closing allowEmpty
        (input := { input with cursor := input.cursor + 1 }) continues
      rcases rejectComplete (input := { input with cursor := input.cursor + 1 }) childRejected with
        ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by
        simp only [delimitedNoTrailing, delimitedWithPolicy, openingResult, guard,
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
      have tailAtNext : DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace
          elementRejects next.file.id next.window.endByte next.declarativeRemainder after diagnostic tailEvents := by
        simpa only [frame.1, frame.2, nextAfter] using tailRejected
      have adequate : next.remainingCount <
          ({ input with cursor := input.cursor + 1 } : State).remainingCount + 1 := by
        simp only [State.remainingCount, frame.2]
        omega
      rcases afterDelimitedElement_noTrailing_trace_reject_complete successComplete rejectComplete contextFrame
          closing context phase { span := openingSpan, value := .symbol opening }
          (({ input with cursor := input.cursor + 1 } : State).remainingCount + 1) [value]
          tailAtNext adequate with ⟨failure, rejected, tailResult, afterEq, reportEq, diagnostics⟩
      refine ⟨failure, rejected, ?_, afterEq, reportEq, ?_⟩
      · simp only [delimitedNoTrailing, delimitedWithPolicy, openingResult, guard, Bool.false_eq_true,
          if_false, childResult, nextProgress, if_true]
        exact tailResult
      · rw [diagnostics, childEq, List.append_assoc]
        rfl

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingRejectionTraceCorrespondenceProperties
/-! Exact no-trailing rejection iff theorems retain the complete uncommitted
failure and ordered appended diagnostics, including arbitrary incoming events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem delimitedNoTrailing_trace_reject_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace
      elementRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, delimitedNoTrailing opening closing allowEmpty element context phase input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = diagnostic ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact delimitedNoTrailing_trace_reject_complete successComplete rejectComplete contextFrame
      opening closing allowEmpty context phase
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases delimitedNoTrailing_reject_trace_sound successSound rejectSound contextFrame
        opening closing allowEmpty context phase result with ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

theorem delimitedNoTrailing_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase)
    {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NoTrailingDelimitedListTraceRejects opening closing allowEmpty context elementTrace
      elementRejects input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, delimitedNoTrailing opening closing allowEmpty element context phase input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  rw [delimitedNoTrailing_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame opening closing allowEmpty context phase]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingTailRejectionTraceCorrespondenceProperties
/-! Exact rejection correspondences at the no-trailing tail-loop boundary.
Fuel and arbitrary reverse prefixes are explicit; the production wrappers use
the tail input's remaining count, independently of the full-list entry bound. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem afterDelimitedElement_noTrailing_production_trace_reject_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace
      elementRejects input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace) :
    ∃ failure rejected, afterDelimitedElement element closing false context phase opening
        (input.remainingCount + 1) elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_noTrailing_trace_reject_complete successComplete rejectComplete contextFrame
    closing context phase opening (input.remainingCount + 1) elementsRev rejection (by omega)

theorem afterDelimitedElement_noTrailing_trace_reject_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) {input : State} (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, afterDelimitedElement element closing false context phase opening fuel elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      failure.toDiagnostic = diagnostic ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact afterDelimitedElement_noTrailing_trace_reject_complete successComplete rejectComplete contextFrame
      closing context phase opening fuel elementsRev rejection adequate
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases afterDelimitedElement_noTrailing_reject_trace_sound successSound rejectSound contextFrame
        closing context phase opening fuel elementsRev input failure rejected result with
      ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

theorem afterDelimitedElement_noTrailing_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) {input : State} (adequate : input.remainingCount < fuel)
    {after : DeclarativeGrammar.Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, afterDelimitedElement element closing false context phase opening fuel elementsRev input =
        .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  rw [afterDelimitedElement_noTrailing_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame closing context phase opening fuel elementsRev adequate]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, diagnostics⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, diagnostics⟩
  · rintro ⟨rejected, result, afterEq, diagnostics⟩
    exact ⟨failure, rejected, result, afterEq, rfl, diagnostics⟩

theorem afterDelimitedElement_noTrailing_production_trace_reject_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State} {after : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after diagnostic trace ↔
    ∃ failure rejected, afterDelimitedElement element closing false context phase opening
        (input.remainingCount + 1) elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_noTrailing_trace_reject_iff successSound rejectSound successComplete rejectComplete
    contextFrame closing context phase opening (input.remainingCount + 1) elementsRev (by omega)

theorem afterDelimitedElement_noTrailing_production_trace_reject_failure_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (rejectComplete : ParserTraceRejectComplete element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State} {after : DeclarativeGrammar.Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NoTrailingDelimitedTailTraceRejects closing context elementTrace elementRejects
      input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace ↔
    ∃ rejected, afterDelimitedElement element closing false context phase opening
        (input.remainingCount + 1) elementsRev input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_noTrailing_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
    contextFrame closing context phase opening (input.remainingCount + 1) elementsRev (by omega)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingTraceSoundnessProperties
/-! Success reflection with arbitrary reverse prefixes and incoming events.
Only child success trace and source/full-window contracts are required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DelimitedTraceInternals

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem afterDelimitedElement_noTrailing_success_trace_sound
    (successSound : ParserTraceSuccessSound element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values output,
      afterDelimitedElement element closing false context phase opening fuel elementsRev input =
        .ok values output →
      ∃ suffix closingSpan trace,
        values = {
          span := SourceSpan.cover opening.span closingSpan
          elements := elementsRev.reverse ++ suffix } ∧
        DeclarativeGrammar.NoTrailingDelimitedTailTraceParses closing elementTrace
          input.file.id input.window.endByte input.declarativeRemainder suffix
          closingSpan output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input values output result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input values output result
      unfold afterDelimitedElement at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma context commaPresent with ⟨comma, commaResult⟩
        simp only [commaPresent, if_true, commaResult, Bool.false_and, Bool.false_eq_true, if_false]
          at result
        cases elementResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok value next =>
            simp only [elementResult] at result
            split at result
            · rename_i progress
              rcases successSound elementResult with ⟨headEvents, headParsed, headEq⟩
              have frame := contextFrame elementResult
              rcases ih (value :: elementsRev) next values output result with
                ⟨suffix, closingSpan, tailEvents, valuesEq, tailParsed, tailEq⟩
              refine ⟨value :: suffix, closingSpan, headEvents ++ tailEvents, ?_, ?_, ?_⟩
              · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valuesEq
              · exact .next comma.span (symbol_success_exactTokenParses .comma context commaResult)
                  headParsed progress (by simpa only [frame.1, frame.2] using tailParsed)
              · rw [tailEq, headEq]; exact List.append_assoc _ _ _
            · contradiction
      · have commaFalse : isSymbol input .comma = false := Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        split at result
        · rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
            ⟨closingSpan, closingParsed, valuesEq, stateEq⟩
          refine ⟨[], closingSpan, [], ?_, .close
            (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse) closingParsed, ?_⟩
          · simpa only [List.append_nil] using valuesEq
          · rw [stateEq]; simp only [State.diagnostics, List.append_nil]
        · unfold rejectAt at result; contradiction

theorem delimitedNoTrailing_success_trace_sound
    (successSound : ParserTraceSuccessSound element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserTraceSuccessSound (delimitedNoTrailing opening closing allowEmpty element context phase)
      (DeclarativeGrammar.NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace) := by
  intro input output values result
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have marker := symbol_success_exactTokenParses opening context openingResult
      have stateEq := (symbol_ok_tokenAt opening context openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rename_i emptyGuard
        have allowed : allowEmpty = true := by cases allowEmpty <;> simp_all
        rcases closeDelimited_success_trace_sound openingToken closing context [] result with
          ⟨closingSpan, closingParsed, valuesEq, outputEq⟩
        refine ⟨[], ?_, ?_⟩
        · rw [valuesEq]
          exact .empty openingToken.span closingSpan allowed marker closingParsed
        · rw [outputEq]; simp only [State.diagnostics, List.append_nil]
      · rename_i notEmpty
        have continues := preferredCloseNotTaken_of_guard_false closing allowEmpty
          (Bool.eq_false_iff.mpr notEmpty)
        cases elementResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first next =>
            simp only [elementResult] at result
            split at result
            · rename_i progress
              rcases successSound elementResult with ⟨headEvents, headParsed, headEq⟩
              have frame := contextFrame elementResult
              rcases afterDelimitedElement_noTrailing_success_trace_sound successSound contextFrame
                  closing context phase openingToken _ [first] next values output result with
                ⟨suffix, closingSpan, tailEvents, valuesEq, tailParsed, tailEq⟩
              have valueShape : values = {
                  span := SourceSpan.cover openingToken.span closingSpan
                  elements := first :: suffix } := by simpa using valuesEq
              refine ⟨headEvents ++ tailEvents, ?_, ?_⟩
              · rw [valueShape]
                exact .nonempty openingToken.span closingSpan marker continues headParsed progress
                  (by simpa only [frame.1, frame.2] using tailParsed)
              · rw [tailEq, headEq]; exact List.append_assoc _ _ _
            · contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingTraceCompletenessProperties
/-! Independent traces execute with sufficient remaining-token fuel. The
actual full-list bound is the remaining count immediately after opening plus
one, not the count after the first child. No token-carrier law is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DelimitedTraceInternals

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem afterDelimitedElement_noTrailing_trace_success_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α)
    {input : State} {suffix : List α} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.NoTrailingDelimitedTailTraceParses closing elementTrace
      input.file.id input.window.endByte input.declarativeRemainder suffix closingSpan after trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, afterDelimitedElement element closing false context phase opening fuel elementsRev input =
      .ok {
        span := SourceSpan.cover opening.span closingSpan
        elements := elementsRev.reverse ++ suffix } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing elementsRev input suffix closingSpan after trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | close absent finish =>
          rcases (closeDelimited_trace_success_iff opening closing context elementsRev).mp
              ⟨⟨closingSpan, finish, rfl⟩, rfl⟩ with ⟨output, result, afterEq, diagnostics⟩
          refine ⟨output, ?_, afterEq, diagnostics⟩
          simpa only [afterDelimitedElement, symbol_absent .comma absent, Bool.false_eq_true, if_false,
            symbol_present closing finish, if_true, List.append_nil] using result
      | next commaSpan comma headParsed progress tailParsed =>
          rename_i afterComma afterElement value rest headEvents tailEvents
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma context comma
          have commaPresent := symbol_present .comma comma
          rcases comma with ⟨commaToken, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) headParsed with
            ⟨next, headResult, afterEq, headEq⟩
          have frame := contextFrame headResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := commaToken.1
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          have tailAtNext : DeclarativeGrammar.NoTrailingDelimitedTailTraceParses closing elementTrace
              next.file.id next.window.endByte next.declarativeRemainder rest closingSpan after tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tailParsed
          rcases ih (value :: elementsRev) tailAtNext nextAdequate with
            ⟨output, tailResult, finalEq, tailEq⟩
          refine ⟨output, ?_, finalEq, ?_⟩
          · simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.false_and,
              Bool.false_eq_true, if_false, headResult, nextProgress]
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using tailResult
          · rw [tailEq, headEq]; exact List.append_assoc _ _ _

theorem afterDelimitedElement_noTrailing_production_trace_success_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State} {suffix : List α} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.NoTrailingDelimitedTailTraceParses closing elementTrace
      input.file.id input.window.endByte input.declarativeRemainder suffix closingSpan after trace) :
    ∃ output, afterDelimitedElement element closing false context phase opening
      (input.remainingCount + 1) elementsRev input = .ok {
        span := SourceSpan.cover opening.span closingSpan
        elements := elementsRev.reverse ++ suffix } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_noTrailing_trace_success_complete successComplete contextFrame
    closing context phase opening (input.remainingCount + 1) elementsRev parsed (by omega)

theorem delimitedNoTrailing_trace_success_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserTraceSuccessComplete (delimitedNoTrailing opening closing allowEmpty element context phase)
      (DeclarativeGrammar.NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace) := by
  intro input values after trace parsed
  cases parsed with
  | empty openingSpan closingSpan allowed marker finish =>
      have markerResult := symbol_eq_ok_of_exactTokenParses opening context marker
      rcases marker with ⟨_, rfl⟩
      have finishPresent := symbol_present closing (input := { input with cursor := input.cursor + 1 }) finish
      have finishResult := symbol_eq_ok_of_exactTokenParses closing context
        (input := { input with cursor := input.cursor + 1 }) finish
      refine ⟨{ input with cursor := input.cursor + 2 }, ?_, finish.2.symm, ?_⟩
      · simp only [delimitedNoTrailing, delimitedWithPolicy, markerResult, allowed, Bool.true_and,
          finishPresent, if_true, closeDelimited, finishResult, List.reverse_nil]
      · simp only [State.diagnostics, List.append_nil]
  | nonempty openingSpan closingSpan marker continues firstParsed progress tailParsed =>
      rename_i afterOpening afterFirst first rest firstEvents tailEvents
      have markerResult := symbol_eq_ok_of_exactTokenParses opening context marker
      rcases marker with ⟨_, rfl⟩
      have guard := guard_false_of_preferredCloseNotTaken closing allowEmpty
        (input := { input with cursor := input.cursor + 1 }) continues
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) firstParsed with
        ⟨next, firstResult, afterEq, firstEq⟩
      have frame := contextFrame firstResult
      have nextProgress : input.cursor + 1 < next.cursor := by
        simpa only [← afterEq, State.declarativeRemainder] using progress
      have adequate : next.remainingCount <
          ({ input with cursor := input.cursor + 1 } : State).remainingCount + 1 := by
        simp only [State.remainingCount, frame.2]
        omega
      have tailAtNext : DeclarativeGrammar.NoTrailingDelimitedTailTraceParses closing elementTrace
          next.file.id next.window.endByte next.declarativeRemainder rest closingSpan after tailEvents := by
        simpa only [frame.1, frame.2, afterEq] using tailParsed
      rcases afterDelimitedElement_noTrailing_trace_success_complete successComplete contextFrame
          closing context phase { span := openingSpan, value := .symbol opening }
          (({ input with cursor := input.cursor + 1 } : State).remainingCount + 1) [first]
          tailAtNext adequate with ⟨output, result, finalEq, diagnostics⟩
      refine ⟨output, ?_, finalEq, ?_⟩
      · simp only [delimitedNoTrailing, delimitedWithPolicy, markerResult, guard, Bool.false_eq_true,
          if_false, firstResult, nextProgress, if_true]
        simpa using result
      · rw [diagnostics, firstEq]; exact List.append_assoc _ _ _

theorem delimitedNoTrailing_trace_success_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase)
    {input : State} {values : DelimitedList α} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.NoTrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      input.file.id input.window.endByte input.declarativeRemainder values after trace ↔
    ∃ output, delimitedNoTrailing opening closing allowEmpty element context phase input = .ok values output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact delimitedNoTrailing_trace_success_complete successComplete contextFrame
      opening closing allowEmpty context phase
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases delimitedNoTrailing_success_trace_sound successSound contextFrame
        opening closing allowEmpty context phase result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- Exact tail equivalence includes the arbitrary already-parsed reverse prefix. -/
theorem afterDelimitedElement_noTrailing_trace_success_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) {input : State}
    (adequate : input.remainingCount < fuel)
    {values : DelimitedList α} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ suffix closingSpan, values = {
        span := SourceSpan.cover opening.span closingSpan
        elements := elementsRev.reverse ++ suffix } ∧
      DeclarativeGrammar.NoTrailingDelimitedTailTraceParses closing elementTrace
        input.file.id input.window.endByte input.declarativeRemainder suffix closingSpan after trace) ↔
    ∃ output, afterDelimitedElement element closing false context phase opening fuel elementsRev input =
      .ok values output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨suffix, closingSpan, rfl, parsed⟩
    exact afterDelimitedElement_noTrailing_trace_success_complete successComplete contextFrame
      closing context phase opening fuel elementsRev parsed adequate
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases afterDelimitedElement_noTrailing_success_trace_sound successSound contextFrame
        closing context phase opening fuel elementsRev input values output result with
      ⟨suffix, closingSpan, actualTrace, valuesEq, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    exact ⟨suffix, closingSpan, valuesEq, by simpa only [afterEq, events] using parsed⟩

theorem afterDelimitedElement_noTrailing_production_trace_success_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State}
    {values : DelimitedList α} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ suffix closingSpan, values = {
        span := SourceSpan.cover opening.span closingSpan
        elements := elementsRev.reverse ++ suffix } ∧
      DeclarativeGrammar.NoTrailingDelimitedTailTraceParses closing elementTrace
        input.file.id input.window.endByte input.declarativeRemainder suffix closingSpan after trace) ↔
    ∃ output, afterDelimitedElement element closing false context phase opening
      (input.remainingCount + 1) elementsRev input = .ok values output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_noTrailing_trace_success_iff successSound successComplete contextFrame
    closing context phase opening (input.remainingCount + 1) elementsRev (by omega)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedNoTrailingTraceContextProperties
/-! Successful no-trailing lists preserve source and the entire active window
under exactly the corresponding child law, independently of token carriers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {α : Type} {element : Parser α}

theorem afterDelimitedElement_noTrailing_success_context
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values output,
      afterDelimitedElement element closing false context phase opening fuel elementsRev input =
        .ok values output → output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input values output result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input values output result
      unfold afterDelimitedElement at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma context commaPresent with ⟨comma, commaResult⟩
        simp only [commaPresent, if_true, commaResult, Bool.false_and, Bool.false_eq_true, if_false]
          at result
        cases elementResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok value next =>
            simp only [elementResult] at result
            split at result
            · have frame := contextFrame elementResult
              have tail := ih (value :: elementsRev) next values output result
              exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
            · contradiction
      · have commaFalse : isSymbol input .comma = false := Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        split at result
        · rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
            ⟨_, _, _, stateEq⟩
          rw [stateEq]; exact ⟨rfl, rfl⟩
        · unfold rejectAt at result; contradiction

theorem delimitedNoTrailing_success_context
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserSuccessContext (delimitedNoTrailing opening closing allowEmpty element context phase) := by
  intro input output values result
  unfold delimitedNoTrailing delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have stateEq := (symbol_ok_tokenAt opening context openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rcases closeDelimited_success_trace_sound openingToken closing context [] result with
          ⟨_, _, _, outputEq⟩
        rw [outputEq]; exact ⟨rfl, rfl⟩
      · cases elementResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first next =>
            simp only [elementResult] at result
            split at result
            · have frame := contextFrame elementResult
              have tail := afterDelimitedElement_noTrailing_success_context contextFrame
                closing context phase openingToken _ [first] next values output result
              exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
            · contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceSoundnessProperties
/-! Exact trailing-enabled rejection reflection. Earlier child diagnostics survive
in order and the final report remains uncommitted. Successful source/window
preservation is explicit; no token-carrier or rejected-state frame is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DelimitedTraceInternals

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

/-- Every fixed-fuel tail rejection reflects its exact report and event suffix,
independently of the arbitrary already-accumulated reverse element prefix. -/
theorem afterDelimitedElement_trailing_reject_trace_sound
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input failure rejected,
      afterDelimitedElement element closing true context phase opening fuel elementsRev input =
        .reject failure rejected →
      ∃ trace, DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context elementTrace
        elementRejects input.file.id input.window.endByte input.declarativeRemainder
          rejected.declarativeRemainder failure.toDiagnostic trace ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input failure rejected result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input failure rejected result
      unfold afterDelimitedElement at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma context commaPresent with ⟨comma, commaResult⟩
        have commaParsed := symbol_success_exactTokenParses .comma context commaResult
        simp only [commaPresent, if_true, commaResult, Bool.true_and] at result
        by_cases closingPresent : isSymbol { input with cursor := input.cursor + 1 } closing = true
        · rcases symbol_eq_ok_of_isSymbol_eq_true closing context closingPresent with ⟨token, parsed⟩
          simp only [closingPresent, if_true, closeDelimited, parsed] at result
          contradiction
        · have closingFalse := Bool.eq_false_iff.mpr closingPresent
          have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false closing closingFalse
          simp only [closingFalse, Bool.false_eq_true, if_false] at result
          cases childResult : element { input with cursor := input.cursor + 1 } with
          | invariant error => simp [childResult] at result
          | reject childFailure childRejected =>
              simp only [childResult] at result
              cases result
              rcases rejectSound childResult with ⟨trace, childRejected, diagnostics⟩
              exact ⟨trace, .elementRejected comma.span commaParsed closingAbsent childRejected, diagnostics⟩
          | ok value next =>
              simp only [childResult] at result
              by_cases progress : next.cursor > input.cursor + 1
              · simp only [progress, if_true] at result
                rcases ih (value :: elementsRev) next failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
                rcases successSound childResult with ⟨childEvents, childParsed, childEq⟩
                have frame := contextFrame childResult
                have tailAtInput : DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context
                    elementTrace elementRejects input.file.id input.window.endByte next.declarativeRemainder
                    rejected.declarativeRemainder failure.toDiagnostic tailEvents := by
                  simpa only [frame.1, frame.2] using tailRejected
                refine ⟨childEvents ++ tailEvents,
                  .laterRejected comma.span commaParsed closingAbsent childParsed progress tailAtInput, ?_⟩
                rw [tailEq, childEq, List.append_assoc]
                rfl
              · simp only [progress, if_false] at result
                contradiction
      · have commaFalse := Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        by_cases closingPresent : isSymbol input closing = true
        · rcases symbol_eq_ok_of_isSymbol_eq_true closing context closingPresent with ⟨token, parsed⟩
          simp [closingPresent, closeDelimited, parsed] at result
        · have closingFalse := Bool.eq_false_iff.mpr closingPresent
          simp only [closingFalse, Bool.false_eq_true, if_false] at result
          have reported := rejectAt_reject_reports { head := .symbol .comma, tail := [.symbol closing] }
            context result
          unfold rejectAt at result
          cases result
          exact ⟨[], .delimiterMissing (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse)
            (symbolAbsentAt_of_isSymbol_eq_false closing closingFalse) reported.1, by simp⟩

/-- Complete list reflection retains opening/first-child/tail first-failure
priority under either empty policy, with arbitrary incoming diagnostics. -/
theorem delimited_reject_trace_sound
    (successSound : ParserTraceSuccessSound element elementTrace)
    (rejectSound : ParserTraceRejectSound element elementRejects)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserTraceRejectSound (delimited opening closing allowEmpty element context phase)
      (DeclarativeGrammar.TrailingDelimitedListTraceRejects opening closing allowEmpty context
        elementTrace elementRejects) := by
  intro input rejected failure result
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have shape := symbol_reject_state_eq opening context openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      have reported := (symbol_reject_reports_iff opening context).mpr ⟨failure, openingResult, rfl⟩
      exact ⟨[], .openingMissing reported.1 reported.2, by simp⟩
  | ok openingToken afterOpening =>
      have openingParsed := symbol_success_exactTokenParses opening context openingResult
      have shape := (symbol_ok_tokenAt opening context openingResult).2
      simp only [openingResult] at result
      by_cases emptyClose : (allowEmpty && isSymbol afterOpening closing) = true
      · have closingPresent : isSymbol afterOpening closing = true := by
          cases allowEmpty with
          | false => simp at emptyClose
          | true => simpa using emptyClose
        rcases symbol_eq_ok_of_isSymbol_eq_true closing context closingPresent with ⟨token, parsed⟩
        simp [emptyClose, closeDelimited, parsed] at result
      · have emptyFalse := Bool.eq_false_iff.mpr emptyClose
        have continues := preferredCloseNotTaken_of_guard_false closing allowEmpty emptyFalse
        simp only [emptyFalse, Bool.false_eq_true, if_false] at result
        cases childResult : element afterOpening with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            rcases rejectSound childResult with ⟨trace, childRejected, diagnostics⟩
            refine ⟨trace, .firstRejected openingToken.span openingParsed continues ?_, ?_⟩
            · simpa only [shape] using childRejected
            · simpa only [shape, State.diagnostics] using diagnostics
        | ok value next =>
            simp only [childResult] at result
            by_cases progress : next.cursor > afterOpening.cursor
            · simp only [progress, if_true] at result
              rcases afterDelimitedElement_trailing_reject_trace_sound successSound rejectSound contextFrame
                  closing context phase openingToken (afterOpening.remainingCount + 1) [value] next
                  failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
              rcases successSound childResult with ⟨childEvents, childParsed, childEq⟩
              have frame := contextFrame childResult
              have childAtInput : elementTrace input.file.id input.window.endByte afterOpening.declarativeRemainder
                  value next.declarativeRemainder childEvents := by simpa only [shape] using childParsed
              have tailAtInput : DeclarativeGrammar.TrailingDelimitedTailTraceRejects closing context
                  elementTrace elementRejects input.file.id input.window.endByte next.declarativeRemainder
                  rejected.declarativeRemainder failure.toDiagnostic tailEvents := by
                simpa only [frame.1, frame.2, shape] using tailRejected
              refine ⟨childEvents ++ tailEvents,
                .tailRejected openingToken.span openingParsed continues childAtInput progress tailAtInput, ?_⟩
              rw [tailEq, childEq, List.append_assoc]
              simp only [shape, State.diagnostics]
            · simp only [progress, if_false] at result
              contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceCompletenessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceCorrespondenceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceTailCorrespondenceProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTrailingTraceSoundnessProperties
/-! Success reflection with arbitrary reverse prefixes and incoming events.
Only child success trace and source/full-window contracts are required. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DelimitedTraceInternals

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem afterDelimitedElement_trailing_success_trace_sound
    (successSound : ParserTraceSuccessSound element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values output,
      afterDelimitedElement element closing true context phase opening fuel elementsRev input =
        .ok values output →
      ∃ suffix closingSpan trace,
        values = {
          span := SourceSpan.cover opening.span closingSpan
          elements := elementsRev.reverse ++ suffix } ∧
        DeclarativeGrammar.TrailingDelimitedTailTraceParses closing elementTrace
          input.file.id input.window.endByte input.declarativeRemainder suffix
          closingSpan output.declarativeRemainder trace ∧
        output.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input values output result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input values output result
      unfold afterDelimitedElement at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma context commaPresent with ⟨comma, commaResult⟩
        simp only [commaPresent, if_true, commaResult, Bool.true_and] at result
        split at result
        · rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
            ⟨closingSpan, closingParsed, valuesEq, stateEq⟩
          refine ⟨[], closingSpan, [], ?_, .trailing comma.span
            (symbol_success_exactTokenParses .comma context commaResult) closingParsed, ?_⟩
          · simpa only [List.append_nil] using valuesEq
          · rw [stateEq]; simp only [State.diagnostics, List.append_nil]
        · rename_i noClosing
          have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false closing (Bool.eq_false_iff.mpr noClosing)
          cases elementResult : element { input with cursor := input.cursor + 1 } with
          | invariant error => simp [elementResult] at result
          | reject failure rejected => simp [elementResult] at result
          | ok value next =>
              simp only [elementResult] at result
              split at result
              · rename_i progress
                rcases successSound elementResult with ⟨headEvents, headParsed, headEq⟩
                have frame := contextFrame elementResult
                rcases ih (value :: elementsRev) next values output result with
                  ⟨suffix, closingSpan, tailEvents, valuesEq, tailParsed, tailEq⟩
                refine ⟨value :: suffix, closingSpan, headEvents ++ tailEvents, ?_, ?_, ?_⟩
                · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using valuesEq
                · exact .next comma.span (symbol_success_exactTokenParses .comma context commaResult)
                    closingAbsent headParsed progress (by simpa only [frame.1, frame.2] using tailParsed)
                · rw [tailEq, headEq]; exact List.append_assoc _ _ _
              · contradiction
      · have commaFalse : isSymbol input .comma = false := Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        split at result
        · rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
            ⟨closingSpan, closingParsed, valuesEq, stateEq⟩
          refine ⟨[], closingSpan, [], ?_, .close
            (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse) closingParsed, ?_⟩
          · simpa only [List.append_nil] using valuesEq
          · rw [stateEq]; simp only [State.diagnostics, List.append_nil]
        · unfold rejectAt at result; contradiction

theorem delimited_trace_success_sound
    (successSound : ParserTraceSuccessSound element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserTraceSuccessSound (delimited opening closing allowEmpty element context phase)
      (DeclarativeGrammar.TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace) := by
  intro input output values result
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have marker := symbol_success_exactTokenParses opening context openingResult
      have stateEq := (symbol_ok_tokenAt opening context openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rename_i emptyGuard
        have allowed : allowEmpty = true := by cases allowEmpty <;> simp_all
        rcases closeDelimited_success_trace_sound openingToken closing context [] result with
          ⟨closingSpan, closingParsed, valuesEq, outputEq⟩
        refine ⟨[], ?_, ?_⟩
        · rw [valuesEq]
          exact .empty openingToken.span closingSpan allowed marker closingParsed
        · rw [outputEq]; simp only [State.diagnostics, List.append_nil]
      · rename_i notEmpty
        have continues := preferredCloseNotTaken_of_guard_false closing allowEmpty
          (Bool.eq_false_iff.mpr notEmpty)
        cases elementResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first next =>
            simp only [elementResult] at result
            split at result
            · rename_i progress
              rcases successSound elementResult with ⟨headEvents, headParsed, headEq⟩
              have frame := contextFrame elementResult
              rcases afterDelimitedElement_trailing_success_trace_sound successSound contextFrame
                  closing context phase openingToken _ [first] next values output result with
                ⟨suffix, closingSpan, tailEvents, valuesEq, tailParsed, tailEq⟩
              have valueShape : values = {
                  span := SourceSpan.cover openingToken.span closingSpan
                  elements := first :: suffix } := by simpa using valuesEq
              refine ⟨headEvents ++ tailEvents, ?_, ?_⟩
              · rw [valueShape]
                exact .nonempty openingToken.span closingSpan marker continues headParsed progress
                  (by simpa only [frame.1, frame.2] using tailParsed)
              · rw [tailEq, headEq]; exact List.append_assoc _ _ _
            · contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTrailingTraceCompletenessProperties
/-! Independent traces execute with sufficient remaining-token fuel. The
actual full-list bound is the remaining count immediately after opening plus
one, not the count after the first child. No token-carrier law is needed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DelimitedTraceInternals

variable {α : Type} {element : Parser α}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → α →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

theorem afterDelimitedElement_trailing_trace_success_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α)
    {input : State} {suffix : List α} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.TrailingDelimitedTailTraceParses closing elementTrace
      input.file.id input.window.endByte input.declarativeRemainder suffix closingSpan after trace)
    (adequate : input.remainingCount < fuel) :
    ∃ output, afterDelimitedElement element closing true context phase opening fuel elementsRev input =
      .ok {
        span := SourceSpan.cover opening.span closingSpan
        elements := elementsRev.reverse ++ suffix } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  induction fuel generalizing elementsRev input suffix closingSpan after trace with
  | zero => omega
  | succ fuel ih =>
      cases parsed with
      | close absent finish =>
          rcases (closeDelimited_trace_success_iff opening closing context elementsRev).mp
              ⟨⟨closingSpan, finish, rfl⟩, rfl⟩ with ⟨output, result, afterEq, diagnostics⟩
          refine ⟨output, ?_, afterEq, diagnostics⟩
          simpa only [afterDelimitedElement, symbol_absent .comma absent, Bool.false_eq_true, if_false,
            symbol_present closing finish, if_true, List.append_nil] using result
      | trailing commaSpan comma finish =>
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma context comma
          have commaPresent := symbol_present .comma comma
          rcases comma with ⟨_, rfl⟩
          rcases (closeDelimited_trace_success_iff opening closing context elementsRev
              (input := { input with cursor := input.cursor + 1 })).mp
              ⟨⟨closingSpan, finish, rfl⟩, rfl⟩ with ⟨output, result, afterEq, diagnostics⟩
          refine ⟨output, ?_, afterEq, diagnostics⟩
          simpa only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and,
            symbol_present closing (input := { input with cursor := input.cursor + 1 }) finish,
            if_true, List.append_nil] using result
      | next commaSpan comma closingAbsent headParsed progress tailParsed =>
          rename_i afterComma afterElement value rest headEvents tailEvents
          have commaResult := symbol_eq_ok_of_exactTokenParses .comma context comma
          have commaPresent := symbol_present .comma comma
          rcases comma with ⟨commaToken, rfl⟩
          rcases successComplete (input := { input with cursor := input.cursor + 1 }) headParsed with
            ⟨next, headResult, afterEq, headEq⟩
          have frame := contextFrame headResult
          have nextProgress : input.cursor + 1 < next.cursor := by
            simpa only [← afterEq, State.declarativeRemainder] using progress
          have nextAdequate : next.remainingCount < fuel := by
            have inside : input.cursor < input.window.endIndex := commaToken.1
            simp only [State.remainingCount, frame.2] at adequate ⊢
            omega
          have tailAtNext : DeclarativeGrammar.TrailingDelimitedTailTraceParses closing elementTrace
              next.file.id next.window.endByte next.declarativeRemainder rest closingSpan after tailEvents := by
            simpa only [frame.1, frame.2, afterEq] using tailParsed
          rcases ih (value :: elementsRev) tailAtNext nextAdequate with
            ⟨output, tailResult, finalEq, tailEq⟩
          refine ⟨output, ?_, finalEq, ?_⟩
          · simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and,
              symbol_absent closing (input := { input with cursor := input.cursor + 1 }) closingAbsent,
              Bool.false_eq_true, if_false, headResult, nextProgress]
            simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using tailResult
          · rw [tailEq, headEq]; exact List.append_assoc _ _ _

theorem afterDelimitedElement_trailing_production_trace_success_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State} {suffix : List α} {closingSpan : SourceSpan}
    {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic}
    (parsed : DeclarativeGrammar.TrailingDelimitedTailTraceParses closing elementTrace
      input.file.id input.window.endByte input.declarativeRemainder suffix closingSpan after trace) :
    ∃ output, afterDelimitedElement element closing true context phase opening
      (input.remainingCount + 1) elementsRev input = .ok {
        span := SourceSpan.cover opening.span closingSpan
        elements := elementsRev.reverse ++ suffix } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_trailing_trace_success_complete successComplete contextFrame
    closing context phase opening (input.remainingCount + 1) elementsRev parsed (by omega)

theorem delimited_trace_success_complete
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserTraceSuccessComplete (delimited opening closing allowEmpty element context phase)
      (DeclarativeGrammar.TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace) := by
  intro input values after trace parsed
  cases parsed with
  | empty openingSpan closingSpan allowed marker finish =>
      have markerResult := symbol_eq_ok_of_exactTokenParses opening context marker
      rcases marker with ⟨_, rfl⟩
      have finishPresent := symbol_present closing (input := { input with cursor := input.cursor + 1 }) finish
      have finishResult := symbol_eq_ok_of_exactTokenParses closing context
        (input := { input with cursor := input.cursor + 1 }) finish
      refine ⟨{ input with cursor := input.cursor + 2 }, ?_, finish.2.symm, ?_⟩
      · simp only [delimited, delimitedWithPolicy, markerResult, allowed, Bool.true_and,
          finishPresent, if_true, closeDelimited, finishResult, List.reverse_nil]
      · simp only [State.diagnostics, List.append_nil]
  | nonempty openingSpan closingSpan marker continues firstParsed progress tailParsed =>
      rename_i afterOpening afterFirst first rest firstEvents tailEvents
      have markerResult := symbol_eq_ok_of_exactTokenParses opening context marker
      rcases marker with ⟨_, rfl⟩
      have guard := guard_false_of_preferredCloseNotTaken closing allowEmpty
        (input := { input with cursor := input.cursor + 1 }) continues
      rcases successComplete (input := { input with cursor := input.cursor + 1 }) firstParsed with
        ⟨next, firstResult, afterEq, firstEq⟩
      have frame := contextFrame firstResult
      have nextProgress : input.cursor + 1 < next.cursor := by
        simpa only [← afterEq, State.declarativeRemainder] using progress
      have adequate : next.remainingCount <
          ({ input with cursor := input.cursor + 1 } : State).remainingCount + 1 := by
        simp only [State.remainingCount, frame.2]
        omega
      have tailAtNext : DeclarativeGrammar.TrailingDelimitedTailTraceParses closing elementTrace
          next.file.id next.window.endByte next.declarativeRemainder rest closingSpan after tailEvents := by
        simpa only [frame.1, frame.2, afterEq] using tailParsed
      rcases afterDelimitedElement_trailing_trace_success_complete successComplete contextFrame
          closing context phase { span := openingSpan, value := .symbol opening }
          (({ input with cursor := input.cursor + 1 } : State).remainingCount + 1) [first]
          tailAtNext adequate with ⟨output, result, finalEq, diagnostics⟩
      refine ⟨output, ?_, finalEq, ?_⟩
      · simp only [delimited, delimitedWithPolicy, markerResult, guard, Bool.false_eq_true,
          if_false, firstResult, nextProgress, if_true]
        simpa using result
      · rw [diagnostics, firstEq]; exact List.append_assoc _ _ _

theorem delimited_trace_success_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase)
    {input : State} {values : DelimitedList α} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    DeclarativeGrammar.TrailingDelimitedListTraceParses opening closing allowEmpty elementTrace
      input.file.id input.window.endByte input.declarativeRemainder values after trace ↔
    ∃ output, delimited opening closing allowEmpty element context phase input = .ok values output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact delimited_trace_success_complete successComplete contextFrame
      opening closing allowEmpty context phase
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases delimited_trace_success_sound successSound contextFrame
        opening closing allowEmpty context phase result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

/-- Exact tail equivalence includes the arbitrary already-parsed reverse prefix. -/
theorem afterDelimitedElement_trailing_trace_success_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (fuel : Nat) (elementsRev : List α) {input : State}
    (adequate : input.remainingCount < fuel)
    {values : DelimitedList α} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ suffix closingSpan, values = {
        span := SourceSpan.cover opening.span closingSpan
        elements := elementsRev.reverse ++ suffix } ∧
      DeclarativeGrammar.TrailingDelimitedTailTraceParses closing elementTrace
        input.file.id input.window.endByte input.declarativeRemainder suffix closingSpan after trace) ↔
    ∃ output, afterDelimitedElement element closing true context phase opening fuel elementsRev input =
      .ok values output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨suffix, closingSpan, rfl, parsed⟩
    exact afterDelimitedElement_trailing_trace_success_complete successComplete contextFrame
      closing context phase opening fuel elementsRev parsed adequate
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases afterDelimitedElement_trailing_success_trace_sound successSound contextFrame
        closing context phase opening fuel elementsRev input values output result with
      ⟨suffix, closingSpan, actualTrace, valuesEq, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    exact ⟨suffix, closingSpan, valuesEq, by simpa only [afterEq, events] using parsed⟩

theorem afterDelimitedElement_trailing_production_trace_success_iff
    (successSound : ParserTraceSuccessSound element elementTrace)
    (successComplete : ParserTraceSuccessComplete element elementTrace)
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token)
    (elementsRev : List α) {input : State}
    {values : DelimitedList α} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    (∃ suffix closingSpan, values = {
        span := SourceSpan.cover opening.span closingSpan
        elements := elementsRev.reverse ++ suffix } ∧
      DeclarativeGrammar.TrailingDelimitedTailTraceParses closing elementTrace
        input.file.id input.window.endByte input.declarativeRemainder suffix closingSpan after trace) ↔
    ∃ output, afterDelimitedElement element closing true context phase opening
      (input.remainingCount + 1) elementsRev input = .ok values output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  afterDelimitedElement_trailing_trace_success_iff successSound successComplete contextFrame
    closing context phase opening (input.remainingCount + 1) elementsRev (by omega)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedTrailingTraceContextProperties
/-! Successful trailing-enabled lists preserve source and the entire active window
under exactly the corresponding child law, independently of token carriers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {α : Type} {element : Parser α}

theorem afterDelimitedElement_trailing_success_context
    (contextFrame : ParserSuccessContext element)
    (closing : Symbol) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values output,
      afterDelimitedElement element closing true context phase opening fuel elementsRev input =
        .ok values output → output.file = input.file ∧ output.window = input.window := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input values output result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input values output result
      unfold afterDelimitedElement at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma context commaPresent with ⟨comma, commaResult⟩
        simp only [commaPresent, if_true, commaResult, Bool.true_and] at result
        split at result
        · rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
            ⟨_, _, _, stateEq⟩
          rw [stateEq]; exact ⟨rfl, rfl⟩
        · cases elementResult : element { input with cursor := input.cursor + 1 } with
          | invariant error => simp [elementResult] at result
          | reject failure rejected => simp [elementResult] at result
          | ok value next =>
              simp only [elementResult] at result
              split at result
              · have frame := contextFrame elementResult
                have tail := ih (value :: elementsRev) next values output result
                exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
              · contradiction
      · have commaFalse : isSymbol input .comma = false := Bool.eq_false_iff.mpr commaPresent
        simp only [commaFalse, Bool.false_eq_true, if_false] at result
        split at result
        · rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
            ⟨_, _, _, stateEq⟩
          rw [stateEq]; exact ⟨rfl, rfl⟩
        · unfold rejectAt at result; contradiction

theorem delimited_success_context
    (contextFrame : ParserSuccessContext element)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase) :
    ParserSuccessContext (delimited opening closing allowEmpty element context phase) := by
  intro input output values result
  unfold delimited delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have stateEq := (symbol_ok_tokenAt opening context openingResult).2
      subst afterOpening
      simp only [openingResult] at result
      split at result
      · rcases closeDelimited_success_trace_sound openingToken closing context [] result with
          ⟨_, _, _, outputEq⟩
        rw [outputEq]; exact ⟨rfl, rfl⟩
      · cases elementResult : element { input with cursor := input.cursor + 1 } with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first next =>
            simp only [elementResult] at result
            split at result
            · have frame := contextFrame elementResult
              have tail := afterDelimitedElement_trailing_success_context contextFrame
                closing context phase openingToken _ [first] next values output result
              exact ⟨tail.1.trans frame.1, tail.2.trans frame.2⟩
            · contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DelimitedUnrestrictedFuelTotalityProperties
/-! Actual delimited loops are ordinary on arbitrary states under the minimal
child fuel contract. Opening/comma tokens pay recursive units before child
execution; child success only preserves the resulting remaining-count bound. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeDelimited_unrestricted_ordinary {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α) :
    Parser.Ordinary (closeDelimited opening closing context elementsRev) := by
  intro input
  rcases symbol_ordinary closing context input with
    ⟨token, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨{ span := SourceSpan.cover opening.span token.span, elements := elementsRev.reverse },
      next, by unfold closeDelimited; simp only [result]⟩
  · exact Or.inr ⟨failure, next, by unfold closeDelimited; simp only [result]⟩

theorem afterDelimitedElement_ordinary_of_unrestrictedElementFuel {α : Type}
    (element : Parser α) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract element elementFuel)
    (closing : Symbol) (allowTrailing : Bool)
    (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ loopFuel elementsRev input,
      input.remainingCount < loopFuel → input.remainingCount < elementFuel →
      (∃ values next, afterDelimitedElement element closing allowTrailing context phase
        opening loopFuel elementsRev input = .ok values next) ∨
      (∃ failure next, afterDelimitedElement element closing allowTrailing context phase
        opening loopFuel elementsRev input = .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intro elementsRev input loopAdequate elementAdequate; omega
  | succ loopFuel ih =>
      intro elementsRev input loopAdequate elementAdequate
      unfold afterDelimitedElement
      split
      · cases commaResult : symbol .comma context input with
        | invariant error =>
            exact False.elim (symbol_ne_invariant .comma context input error commaResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaLoopAdequate : afterComma.remainingCount < loopFuel :=
              symbol_remainingCount_lt_of_success .comma context commaResult loopAdequate
            have commaElementAdequate : afterComma.remainingCount < elementFuel :=
              symbol_remainingCount_lt_of_success .comma context commaResult (by omega)
            dsimp only
            split
            · exact closeDelimited_unrestricted_ordinary opening closing context elementsRev afterComma
            · cases elementResult : element afterComma with
              | invariant error =>
                  exact False.elim (contract.ne_invariant afterComma commaElementAdequate error elementResult)
              | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
              | ok value next =>
                  have progress := contract.cursorLtOnSuccess elementResult
                  dsimp only
                  split
                  · exact ih (value :: elementsRev) next
                      (contract.remainingCount_lt_of_success elementResult commaLoopAdequate)
                      (contract.remainingCount_lt_of_success elementResult commaElementAdequate)
                  · omega
      · split
        · exact closeDelimited_unrestricted_ordinary opening closing context elementsRev input
        · exact Or.inr ⟨_, input, rfl⟩

theorem delimitedWithPolicy_ordinary_of_unrestrictedElementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool)
    (element : Parser α) (context : ParseContext) (phase : ParserPhase) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract element elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ values next, delimitedWithPolicy opening closing allowEmpty allowTrailing element
      context phase input = .ok values next) ∨
    (∃ failure next, delimitedWithPolicy opening closing allowEmpty allowTrailing element
      context phase input = .reject failure next) := by
  unfold delimitedWithPolicy
  cases openingResult : symbol opening context input with
  | invariant error => exact False.elim (symbol_ne_invariant opening context input error openingResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok openingToken afterOpening =>
      have afterOpeningAdequate : afterOpening.remainingCount < elementFuel :=
        symbol_remainingCount_lt_of_success opening context openingResult adequate
      dsimp only
      split
      · exact closeDelimited_unrestricted_ordinary openingToken closing context [] afterOpening
      · cases elementResult : element afterOpening with
        | invariant error =>
            exact False.elim (contract.ne_invariant afterOpening afterOpeningAdequate error elementResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok value next =>
            have progress := contract.cursorLtOnSuccess elementResult
            dsimp only
            split
            · exact afterDelimitedElement_ordinary_of_unrestrictedElementFuel element elementFuel contract
                closing allowTrailing context phase openingToken (afterOpening.remainingCount + 1) [value] next
                (contract.remainingCount_lt_of_success elementResult (by omega))
                (contract.remainingCount_lt_of_success elementResult afterOpeningAdequate)
            · omega

theorem delimited_ordinary_of_unrestrictedElementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract element elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ values next, delimited opening closing allowEmpty element context phase input = .ok values next) ∨
    (∃ failure next, delimited opening closing allowEmpty element context phase input = .reject failure next) :=
  delimitedWithPolicy_ordinary_of_unrestrictedElementFuel opening closing allowEmpty true
    element context phase elementFuel contract input adequate

theorem delimited_ne_invariant_of_unrestrictedElementFuel {α : Type}
    (opening closing : Symbol) (allowEmpty : Bool) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract element elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) (error : ParserInvariantError) :
    delimited opening closing allowEmpty element context phase input ≠ .invariant error := by
  intro failed
  rcases delimited_ordinary_of_unrestrictedElementFuel opening closing allowEmpty element context phase
      elementFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

private theorem closeDelimited_endIndex_onSuccess {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α)
    {input output : State} {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input = .ok values output) :
    output.window.endIndex = input.window.endIndex := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token next =>
      simp only [closingResult] at result
      cases result
      rw [(symbol_ok_state_shape closing context closingResult).2]

theorem afterDelimitedElement_endIndex_onSuccess {α : Type} {element : Parser α}
    (elementEndIndex : ∀ {input output : State} {value : α}, element input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (closing : Symbol) (allowTrailing : Bool) (context : ParseContext) (phase : ParserPhase) (opening : Token) :
    ∀ fuel elementsRev input values output,
      afterDelimitedElement element closing allowTrailing context phase opening fuel elementsRev input =
        .ok values output → output.window.endIndex = input.window.endIndex := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input values output result; simp [afterDelimitedElement] at result
  | succ fuel ih =>
      intro elementsRev input values output result
      unfold afterDelimitedElement at result
      split at result
      · cases commaResult : symbol .comma context input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok token afterComma =>
            have commaEndIndex : afterComma.window.endIndex = input.window.endIndex := by
              rw [(symbol_ok_state_shape .comma context commaResult).2]
            simp only [commaResult] at result
            split at result
            · exact (closeDelimited_endIndex_onSuccess opening closing context elementsRev result).trans commaEndIndex
            · cases elementResult : element afterComma with
              | invariant error => simp [elementResult] at result
              | reject failure rejected => simp [elementResult] at result
              | ok value next =>
                  simp only [elementResult] at result
                  split at result
                  · exact (ih (value :: elementsRev) next values output result).trans
                      ((elementEndIndex elementResult).trans commaEndIndex)
                  · contradiction
      · split at result
        · exact closeDelimited_endIndex_onSuccess opening closing context elementsRev result
        · unfold rejectAt at result; contradiction

theorem delimitedWithPolicy_endIndex_onSuccess {α : Type} {element : Parser α}
    (elementEndIndex : ∀ {input output : State} {value : α}, element input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (opening closing : Symbol) (allowEmpty allowTrailing : Bool) (context : ParseContext) (phase : ParserPhase)
    {input output : State} {values : DelimitedList α}
    (result : delimitedWithPolicy opening closing allowEmpty allowTrailing element context phase input =
      .ok values output) : output.window.endIndex = input.window.endIndex := by
  unfold delimitedWithPolicy at result
  cases openingResult : symbol opening context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok openingToken afterOpening =>
      have openingEndIndex : afterOpening.window.endIndex = input.window.endIndex := by
        rw [(symbol_ok_state_shape opening context openingResult).2]
      simp only [openingResult] at result
      split at result
      · exact (closeDelimited_endIndex_onSuccess openingToken closing context [] result).trans openingEndIndex
      · cases elementResult : element afterOpening with
        | invariant error => simp [elementResult] at result
        | reject failure rejected => simp [elementResult] at result
        | ok first next =>
            simp only [elementResult] at result
            split at result
            · exact (afterDelimitedElement_endIndex_onSuccess elementEndIndex closing allowTrailing
                context phase openingToken _ [first] next values output result).trans
                ((elementEndIndex elementResult).trans openingEndIndex)
            · contradiction

theorem delimited_endIndex_onSuccess {α : Type} {element : Parser α}
    (elementEndIndex : ∀ {input output : State} {value : α}, element input = .ok value output →
      output.window.endIndex = input.window.endIndex)
    (opening closing : Symbol) (allowEmpty : Bool) (context : ParseContext) (phase : ParserPhase)
    {input output : State} {values : DelimitedList α}
    (result : delimited opening closing allowEmpty element context phase input = .ok values output) :
    output.window.endIndex = input.window.endIndex :=
  delimitedWithPolicy_endIndex_onSuccess elementEndIndex opening closing allowEmpty true context phase result

end Solcore.Syntax.Parser
end
