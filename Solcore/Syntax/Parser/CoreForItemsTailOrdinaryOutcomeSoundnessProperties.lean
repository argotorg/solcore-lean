import Solcore.Syntax.Parser.CoreForItemsTailOrdinaryRejectionSoundnessProperties

/-! Packaged executable ordinary outcomes for Core `for` item-list tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/-- Package success with reverse-accumulator order and exact tail rejection. -/
theorem forItemsTail_ordinaryOutcome_sound
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
    (∀ fuel itemsRev input items output,
      forItemsTail expression stop fuel itemsRev input = .ok items output →
        ∃ suffix,
          items = itemsRev.reverse ++ suffix ∧
          DeclarativeGrammar.ForItemsTailOrdinaryParses expressionOrdinary
            stop input.declarativeRemainder suffix
              output.declarativeRemainder) ∧
    (∀ fuel itemsRev input failure rejected,
      forItemsTail expression stop fuel itemsRev input =
          .reject failure rejected →
        DeclarativeGrammar.ForItemsTailRejects expressionOrdinary
          expressionRejects stop input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨forItemsTail_success_ordinary_sound expression stop expressionOrdinary
      expressionSuccessSound,
    forItemsTail_reject_ordinary_sound expression stop expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic Core `for` tail outcomes. -/
theorem forItemsTail_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) (stop : Symbol) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForItemsTailOrdinaryParses expressionOrdinary stop)
      (DeclarativeGrammar.ForItemsTailRejects expressionOrdinary
        expressionRejects stop) :=
  DeclarativeGrammar.forItemsTailDeterministicOutcomeSpec expressionOutcomes
    stop

end Solcore.Syntax.Parser.ControlInternals
