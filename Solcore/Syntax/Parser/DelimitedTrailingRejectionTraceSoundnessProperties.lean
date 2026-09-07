import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceGrammar
import Solcore.Syntax.Parser.DelimitedClosingTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties

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
