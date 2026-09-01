import Solcore.Syntax.Parser.CoreForItemOrdinaryRejectionSoundnessProperties

/-! Packaged ordinary outcomes for one Core `for`-header item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

/-- Package executable `for let` success and exact rejection. -/
theorem forLetItem_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {item : ForItem},
      forLetItem expression input = .ok item output →
        DeclarativeGrammar.ForLetItemOrdinaryParses expressionOrdinary
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forLetItem expression input = .reject failure rejected →
        DeclarativeGrammar.ForLetItemRejects expressionOrdinary
          expressionRejects DeclarativeGrammar.TypeExprRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨forLetItem_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    forLetItem_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionRejectSound⟩

/-- Re-export deterministic `for let` outcomes with the fixed public Core
type outcome. -/
theorem forLetItem_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForLetItemOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ForLetItemRejects expressionOrdinary
        expressionRejects DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.forLetItemDeterministicOutcomeSpec expressionOutcomes
    DeclarativeGrammar.typeExprDeterministicOutcomeSpec

/-- Package executable assignment/expression-item success and rejection. -/
theorem forAssignmentOrExpression_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {item : ForItem},
      forAssignmentOrExpression expression input = .ok item output →
        DeclarativeGrammar.ForAssignmentOrExpressionOrdinaryParses
          expressionOrdinary input.declarativeRemainder item
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forAssignmentOrExpression expression input = .reject failure rejected →
        DeclarativeGrammar.ForAssignmentOrExpressionRejects
          expressionOrdinary expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨forAssignmentOrExpression_success_ordinary_sound expression
      expressionOrdinary expressionSuccessSound,
    forAssignmentOrExpression_reject_ordinary_sound expression
      expressionOrdinary expressionRejects expressionSuccessSound
        expressionRejectSound⟩

/-- Re-export deterministic fallback-item outcomes. -/
theorem forAssignmentOrExpression_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForAssignmentOrExpressionOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.ForAssignmentOrExpressionRejects
        expressionOrdinary expressionRejects) :=
  DeclarativeGrammar.forAssignmentOrExpressionDeterministicOutcomeSpec
    expressionOutcomes

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

/-- Package both outcomes of the executable let-prioritized dispatcher. -/
theorem forItem_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder) :
    (∀ {input output : State} {item : ForItem},
      forItem expression input = .ok item output →
        DeclarativeGrammar.ForItemOrdinaryParses expressionOrdinary
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forItem expression input = .reject failure rejected →
        DeclarativeGrammar.ForItemRejects expressionOrdinary
          expressionRejects DeclarativeGrammar.TypeExprRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨forItem_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    forItem_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic public-item outcomes. -/
theorem forItem_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForItemOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ForItemRejects expressionOrdinary
        expressionRejects DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.forItemDeterministicOutcomeSpec expressionOutcomes
    DeclarativeGrammar.typeExprDeterministicOutcomeSpec

end Solcore.Syntax.Parser
