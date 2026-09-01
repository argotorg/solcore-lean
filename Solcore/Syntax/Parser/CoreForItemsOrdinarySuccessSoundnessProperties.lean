import Solcore.Syntax.DeclarativeCoreForItemsOutcomeProperties
import Solcore.Syntax.Parser.CoreForItemSoundnessProperties
import Solcore.Syntax.Parser.CoreForItemsTailOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Executable ordinary success for public Core `for` item lists. -/

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

/-- Every public success is the non-consuming prioritized stop or a forward
list with one progressing first item and its exact tail. -/
theorem forItems_success_ordinary_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    {input output : State} {items : List ForItem}
    (result : forItems expression stop input = .ok items output) :
    DeclarativeGrammar.ForItemsOrdinaryParses expressionOrdinary stop
      input.declarativeRemainder items output.declarativeRemainder := by
  unfold forItems at result
  cases stopPresent : isSymbol input stop with
  | true =>
      simp only [stopPresent, if_true] at result
      cases result
      rcases symbolTokenAt_of_isSymbol_eq_true stop stopPresent with
        ⟨stopSpan, stopCurrent⟩
      exact .empty stopSpan stopCurrent
  | false =>
      simp only [stopPresent, Bool.false_eq_true, if_false] at result
      cases itemResult : forItem expression input with
      | invariant error => simp [itemResult] at result
      | reject failure rejected => simp [itemResult] at result
      | ok first afterFirst =>
          simp only [itemResult] at result
          rcases forItemsTail_success_ordinary_sound expression stop
              expressionOrdinary expressionSuccessSound
              (afterFirst.remainingCount + 1) [first] afterFirst items output
                result with
            ⟨suffix, itemsEq, tailParsed⟩
          have progress := forItem_cursor_lt_onSuccess_of_expressionStrict
            expression expressionStrict itemResult
          rw [itemsEq]
          simpa using DeclarativeGrammar.ForItemsParses.nonempty
            (symbolAbsentAt_of_isSymbol_eq_false stop stopPresent)
            (forItem_success_ordinary_sound expression expressionOrdinary
              expressionSuccessSound itemResult)
            (by simpa [State.declarativeRemainder] using progress)
            tailParsed

end Solcore.Syntax.Parser.ControlInternals
