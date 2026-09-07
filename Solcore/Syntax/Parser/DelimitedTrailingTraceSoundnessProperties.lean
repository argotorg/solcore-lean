import Solcore.Syntax.Parser.DelimitedClosingTraceProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceGrammar

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
