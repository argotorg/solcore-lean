import Solcore.Syntax.Parser.TupleTailRejectionTraceSoundnessProperties

/-! Raw parenthesized rejection reflection, including a missing opening token.
The tail route explicitly records the comma selected after the first child. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

variable {nested : Parser Expr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → Expr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

theorem parenthesized_reject_trace_sound
    (successSound : ExpressionTraceSuccessSound nested elementTrace)
    (rejectSound : ExpressionTraceRejectSound nested elementRejects)
    (contextFrame : ExpressionSuccessContext nested) :
    ExpressionTraceRejectSound (parenthesized nested)
      (DeclarativeGrammar.ParenthesizedExpressionTraceRejects elementTrace elementRejects) := by
  intro input rejected failure result
  unfold parenthesized at result
  cases openingResult : symbol .leftParen .expression input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      have shape := symbol_reject_state_eq .leftParen .expression openingResult
      subst openingRejected
      simp only [openingResult] at result
      cases result
      have reported := (symbol_reject_reports_iff .leftParen .expression).mpr ⟨failure, openingResult, rfl⟩
      exact ⟨[], .openingMissing reported.1 reported.2, by simp⟩
  | ok opening afterOpening =>
      have openingParsed := symbol_success_exactTokenParses .leftParen .expression openingResult
      have shape := (symbol_ok_tokenAt .leftParen .expression openingResult).2
      simp only [openingResult] at result
      by_cases closingPresent : isSymbol afterOpening .rightParen = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .rightParen .expression closingPresent with ⟨closing, closingResult⟩
        simp [closingPresent, closeTuple_eq_of_symbol, closingResult] at result
      · have closingFalse := Bool.eq_false_iff.mpr closingPresent
        have closingAbsent := symbolAbsentAt_of_isSymbol_eq_false .rightParen closingFalse
        simp only [closingFalse, Bool.false_eq_true, if_false] at result
        cases childResult : nested afterOpening with
        | invariant error => simp [childResult] at result
        | reject childFailure childRejected =>
            simp only [childResult] at result
            cases result
            rcases rejectSound childResult with ⟨trace, childRejected, diagnostics⟩
            refine ⟨trace, .firstRejected opening.span openingParsed closingAbsent ?_, ?_⟩
            · simpa only [shape] using childRejected
            · simpa only [shape, State.diagnostics] using diagnostics
        | ok first next =>
            simp only [childResult] at result
            by_cases noProgress : next.cursor ≤ afterOpening.cursor
            · simp only [noProgress, if_true] at result
              contradiction
            · simp only [noProgress, if_false] at result
              have progress : afterOpening.cursor < next.cursor := Nat.lt_of_not_ge noProgress
              rcases successSound childResult with ⟨childEvents, childParsed, childEq⟩
              have frame := contextFrame childResult
              have childAtInput : elementTrace input.file.id input.window.endByte afterOpening.declarativeRemainder
                  first next.declarativeRemainder childEvents := by simpa only [shape] using childParsed
              by_cases commaPresent : isSymbol next .comma = true
              · simp only [commaPresent, if_true] at result
                rcases symbol_eq_ok_of_isSymbol_eq_true .comma .expression commaPresent with ⟨comma, commaResult⟩
                rcases tupleTail_reject_trace_sound successSound rejectSound contextFrame opening
                  (next.remainingCount + 1) [first] next failure rejected result with ⟨tailEvents, tailRejected, tailEq⟩
                have tailAtInput : DeclarativeGrammar.ParenthesizedTupleTailTraceRejects elementTrace elementRejects
                    input.file.id input.window.endByte next.declarativeRemainder rejected.declarativeRemainder
                    failure.toDiagnostic tailEvents := by simpa only [frame.1, frame.2, shape] using tailRejected
                refine ⟨childEvents ++ tailEvents, .tailRejected opening.span comma.span openingParsed closingAbsent
                  childAtInput progress (symbol_ok_tokenAt .comma .expression commaResult).1 tailAtInput, ?_⟩
                rw [tailEq, childEq, List.append_assoc]
                simp only [shape, State.diagnostics]
              · have commaFalse := Bool.eq_false_iff.mpr commaPresent
                simp only [commaFalse, Bool.false_eq_true, if_false] at result
                have rejectedEq := closeTuple_reject_state_eq opening [first] result
                subst rejected
                have reported := (closeTuple_reject_reports_iff opening [first]).mpr ⟨failure, result, rfl⟩
                refine ⟨childEvents, .closingMissing opening.span openingParsed closingAbsent childAtInput progress
                  (symbolAbsentAt_of_isSymbol_eq_false .comma commaFalse) reported.1 ?_, ?_⟩
                · simpa only [frame.1, frame.2, shape] using reported.2
                · simpa only [shape, State.diagnostics] using childEq

end Solcore.Syntax.Parser.ExpressionAtomInternals
