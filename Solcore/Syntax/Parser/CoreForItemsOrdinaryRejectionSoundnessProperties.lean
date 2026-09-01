import Solcore.Syntax.Parser.CoreForItemsOrdinarySuccessSoundnessProperties

/-! Executable exact rejection for public Core `for` item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Every public rejection follows stop absence and then the rejected first
item or a progressing first item followed by exact tail rejection. -/
theorem forItems_reject_ordinary_sound
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
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    {input rejected : State} {failure : Failure}
    (result : forItems expression stop input = .reject failure rejected) :
    DeclarativeGrammar.ForItemsRejects expressionOrdinary expressionRejects
      stop input.declarativeRemainder rejected.declarativeRemainder := by
  unfold forItems at result
  cases stopPresent : isSymbol input stop with
  | true => simp [stopPresent] at result
  | false =>
      simp only [stopPresent, Bool.false_eq_true, if_false] at result
      have stopAbsent := symbolAbsentAt_of_isSymbol_eq_false stop stopPresent
      cases itemResult : forItem expression input with
      | invariant error => simp [itemResult] at result
      | reject itemFailure itemRejected =>
          simp only [itemResult] at result
          cases result
          exact .firstRejected stopAbsent
            (forItem_reject_ordinary_sound expression expressionOrdinary
              expressionRejects expressionSuccessSound expressionRejectSound
                itemResult)
      | ok first afterFirst =>
          simp only [itemResult] at result
          have progress := forItem_cursor_lt_onSuccess_of_expressionStrict
            expression expressionStrict itemResult
          exact .tailRejected stopAbsent
            (forItem_success_ordinary_sound expression expressionOrdinary
              expressionSuccessSound itemResult)
            (by simpa [State.declarativeRemainder] using progress)
            (forItemsTail_reject_ordinary_sound expression stop
              expressionOrdinary expressionRejects expressionSuccessSound
                expressionRejectSound (afterFirst.remainingCount + 1)
                  [first] afterFirst failure rejected result)

end Solcore.Syntax.Parser.ControlInternals
