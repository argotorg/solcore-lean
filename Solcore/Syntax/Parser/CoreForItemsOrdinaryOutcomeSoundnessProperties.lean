import Solcore.Syntax.Parser.CoreForItemsOrdinaryRejectionSoundnessProperties

/-! Packaged executable ordinary outcomes for public Core `for` item lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Package executable success and exact rejection for public item lists. -/
theorem forItems_ordinaryOutcome_sound
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
      expression input = .ok value output → input.cursor < output.cursor) :
    (∀ {input output : State} {items : List ForItem},
      forItems expression stop input = .ok items output →
        DeclarativeGrammar.ForItemsOrdinaryParses expressionOrdinary stop
          input.declarativeRemainder items output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forItems expression stop input = .reject failure rejected →
        DeclarativeGrammar.ForItemsRejects expressionOrdinary
          expressionRejects stop input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨forItems_success_ordinary_sound expression stop expressionOrdinary
      expressionSuccessSound expressionStrict,
    forItems_reject_ordinary_sound expression stop expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound
        expressionStrict⟩

/-- Re-export deterministic public Core `for` item-list outcomes. -/
theorem forItems_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) (stop : Symbol) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForItemsOrdinaryParses expressionOrdinary stop)
      (DeclarativeGrammar.ForItemsRejects expressionOrdinary expressionRejects
        stop) :=
  DeclarativeGrammar.forItemsDeterministicOutcomeSpec expressionOutcomes stop

end Solcore.Syntax.Parser.ControlInternals
