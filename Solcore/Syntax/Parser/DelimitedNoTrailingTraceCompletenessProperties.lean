import Solcore.Syntax.Parser.DelimitedNoTrailingTraceSoundnessProperties

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
