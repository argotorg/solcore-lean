import Solcore.Syntax.DeclarativeParenthesizedRejectionTraceGrammar
import Solcore.Syntax.Parser.TupleClosingRejectionTraceProperties

/-! Every raw fixed-fuel tuple-tail rejection reflects the exact uncommitted
report and ordered event suffix. No selection or token-carrier premise. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DelimitedTraceInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem tupleTail_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) (opening : Token) :
    ∀ fuel elementsRev input failure rejected,
      tupleTail nested opening fuel elementsRev input = .reject failure rejected →
      ∃ trace, DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
        input.file.id input.window.endByte input.declarativeRemainder rejected.declarativeRemainder
        failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  intro fuel
  induction fuel with
  | zero => intro elementsRev input failure rejected result; simp [tupleTail] at result
  | succ fuel ih =>
      intro elementsRev input failure rejected result
      unfold tupleTail at result
      cases commaResult : symbol .comma .expression input with
      | invariant error => simp [commaResult] at result
      | reject commaFailure commaRejected =>
          have shape := symbol_reject_state_eq .comma .expression commaResult
          subst commaRejected
          simp only [commaResult] at result
          cases result
          have reported := (symbol_reject_reports_iff .comma .expression).mpr ⟨failure, commaResult, rfl⟩
          exact ⟨[], .commaMissing reported.1 reported.2, by simp⟩
      | ok comma afterComma =>
          have commaParsed := symbol_success_exactTokenParses .comma .expression commaResult
          have shape := (symbol_ok_tokenAt .comma .expression commaResult).2
          simp only [commaResult] at result
          by_cases closingPresent : isSymbol afterComma .rightParen = true
          · rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression closingPresent with ⟨closing, closingResult⟩
            simp [closingPresent, closeTuple_eq_of_symbol, closingResult] at result
          · have closingFalse := Bool.eq_false_iff.mpr closingPresent
            have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen closingFalse
            simp only [closingFalse, Bool.false_eq_true, if_false] at result
            cases childResult : nested afterComma with
            | invariant error => simp [childResult] at result
            | reject childFailure childRejected =>
                simp only [childResult] at result
                cases result
                rcases rejectSound childResult with ⟨trace, childRejected, diagnostics⟩
                refine ⟨trace, .elementRejected comma.span commaParsed closingAbsent ?_, ?_⟩
                · simpa only [shape] using childRejected
                · simpa only [shape, State.diagnostics] using diagnostics
            | ok value next =>
                simp only [childResult] at result
                by_cases progress : next.cursor > afterComma.cursor
                · simp only [progress, if_true] at result
                  rcases successSound childResult with ⟨childEvents, childParsed, childEq⟩
                  have frame := contextFrame childResult
                  have childAtInput : elementTrace input.file.id input.window.endByte afterComma.declarativeRemainder
                      value next.declarativeRemainder childEvents := by simpa only [shape] using childParsed
                  by_cases commaPresent : isSymbol next .comma = true
                  · simp only [commaPresent, if_true] at result
                    rcases symbol_eq_ok_of_isSymbol_eq_true .comma .expression commaPresent with ⟨nextComma, nextResult⟩
                    rcases ih (value :: elementsRev) next failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
                    have tailAtInput : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
                        input.file.id input.window.endByte next.declarativeRemainder rejected.declarativeRemainder
                        failure.toDiagnostic tailEvents := by simpa only [frame.1, frame.2, shape] using tailRejected
                    refine ⟨childEvents ++ tailEvents, .laterRejected comma.span nextComma.span commaParsed closingAbsent
                      childAtInput progress (symbol_ok_tokenAt .comma .expression nextResult).1 tailAtInput, ?_⟩
                    rw [tailEq, childEq, List.append_assoc]
                    simp only [shape, State.diagnostics]
                  · have commaFalse := Bool.eq_false_iff.mpr commaPresent
                    simp only [commaFalse, Bool.false_eq_true, if_false] at result
                    have rejectedEq := closeTuple_reject_state_eq opening (value :: elementsRev) result
                    subst rejected
                    have reported := (closeTuple_reject_reports_iff opening (value :: elementsRev)).mpr ⟨failure, result, rfl⟩
                    refine ⟨childEvents, .closingMissing comma.span commaParsed closingAbsent childAtInput progress
                      (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse) reported.1 ?_, ?_⟩
                    · simpa only [frame.1, frame.2, shape] using reported.2
                    · simpa only [shape, State.diagnostics] using childEq
                · simp only [progress, if_false] at result
                  contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
