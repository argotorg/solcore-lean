import Solcore.Syntax.DeclarativeCoreForItemsTailOutcomeProperties
import Solcore.Syntax.Parser.CoreForItemOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.Statement.Control

/-! Executable ordinary success for reverse-accumulating Core `for` tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- The executable reverse accumulator is the returned prefix, followed by
the exact forward suffix parsed from the current state. -/
theorem forItemsTail_success_ordinary_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder) :
    ∀ fuel itemsRev input items output,
      forItemsTail expression stop fuel itemsRev input = .ok items output →
      ∃ suffix,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.ForItemsTailOrdinaryParses expressionOrdinary stop
          input.declarativeRemainder suffix output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items output result
      simp [forItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input items output result
      unfold forItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp only [commaPresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (symbolAbsentAt_of_isSymbol_eq_false .comma commaPresent)⟩
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .statement input with
          | invariant error => simp [commaResult] at result
          | reject failure rejected => simp [commaResult] at result
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases stopPresent : isSymbol afterComma stop with
              | true =>
                  simp only [stopPresent, if_true] at result
                  unfold rejectAt at result
                  contradiction
              | false =>
                  simp only [stopPresent, Bool.false_eq_true, if_false]
                    at result
                  cases itemResult : forItem expression afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject failure rejected => simp [itemResult] at result
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      by_cases progress : afterItem.cursor > afterComma.cursor
                      · simp only [progress, if_true] at result
                        rcases inductionHypothesis (item :: itemsRev)
                            afterItem items output result with
                          ⟨suffix, itemsEq, tailParsed⟩
                        refine ⟨item :: suffix, ?_,
                          .next comma.span
                            (symbol_success_exactTokenParses .comma .statement
                              commaResult)
                            (symbolAbsentAt_of_isSymbol_eq_false stop
                              stopPresent)
                            (forItem_success_ordinary_sound expression
                              expressionOrdinary expressionSuccessSound
                                itemResult)
                            (by simpa [State.declarativeRemainder] using
                              progress)
                            tailParsed⟩
                        simpa [List.reverse_cons, List.append_assoc] using
                          itemsEq
                      · simp only [progress, if_false] at result
                        contradiction

end Solcore.Syntax.Parser.ControlInternals
