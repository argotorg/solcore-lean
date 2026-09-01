import Solcore.Syntax.Parser.CoreForItemOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreForItemsTailOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Executable exact rejection for Core `for` item-list tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

private theorem symbolTokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .statement present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .statement parsed).1⟩

/-- Every executable tail rejection records the committed comma, stop-after-
comma error, rejected item, or recursively rejected suffix. -/
theorem forItemsTail_reject_ordinary_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    ∀ fuel itemsRev input failure rejected,
      forItemsTail expression stop fuel itemsRev input =
          .reject failure rejected →
      DeclarativeGrammar.ForItemsTailRejects expressionOrdinary
        expressionRejects stop input.declarativeRemainder
          rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input failure rejected result
      simp [forItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input failure rejected result
      unfold forItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp [commaPresent] at result
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .statement input with
          | invariant error => simp [commaResult] at result
          | reject commaFailure commaRejected =>
              rcases symbol_eq_ok_of_isSymbol_eq_true .comma .statement
                commaPresent with ⟨comma, parsed⟩
              rw [parsed] at commaResult
              contradiction
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases stopPresent : isSymbol afterComma stop with
              | true =>
                  simp only [stopPresent, if_true] at result
                  rcases symbolTokenAt_of_isSymbol_eq_true stop stopPresent with
                    ⟨stopSpan, stopCurrent⟩
                  unfold rejectAt at result
                  cases result
                  exact .stopAfterComma comma.span stopSpan
                    (symbol_success_exactTokenParses .comma .statement
                      commaResult)
                    stopCurrent
              | false =>
                  simp only [stopPresent, Bool.false_eq_true, if_false]
                    at result
                  cases itemResult : forItem expression afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject itemFailure itemRejected =>
                      simp only [itemResult] at result
                      cases result
                      exact .itemRejected comma.span
                        (symbol_success_exactTokenParses .comma .statement
                          commaResult)
                        (symbolAbsentAt_of_isSymbol_eq_false stop stopPresent)
                        (forItem_reject_ordinary_sound expression
                          expressionOrdinary expressionRejects
                            expressionSuccessSound expressionRejectSound
                              itemResult)
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      by_cases progress : afterItem.cursor > afterComma.cursor
                      · simp only [progress, if_true] at result
                        exact .laterRejected comma.span
                          (symbol_success_exactTokenParses .comma .statement
                            commaResult)
                          (symbolAbsentAt_of_isSymbol_eq_false stop
                            stopPresent)
                          (forItem_success_ordinary_sound expression
                            expressionOrdinary expressionSuccessSound
                              itemResult)
                          (by simpa [State.declarativeRemainder] using
                            progress)
                          (inductionHypothesis (item :: itemsRev) afterItem
                            failure rejected result)
                      · simp only [progress, if_false] at result
                        contradiction

end Solcore.Syntax.Parser.ControlInternals
