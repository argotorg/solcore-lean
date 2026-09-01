import Solcore.Syntax.Parser.CoreForStatementOrdinaryRejectionSoundnessProperties

/-! Packaged executable ordinary outcomes for complete Core `for`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable success and exact rejection for Core `for`. -/
theorem forStatement_ordinaryOutcome_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementSuccessSound : ∀ {input output : State} {value : Statement},
      statement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      statement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State}
      {failure : Failure}, expression input = .reject failure rejected →
        expressionRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor) :
    (∀ {input output : State} {value : Statement},
      forStatement statement expression input = .ok value output →
        DeclarativeGrammar.ForStatementOrdinaryParses statementOrdinary
          expressionOrdinary input.declarativeRemainder value
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      forStatement statement expression input = .reject failure rejected →
        DeclarativeGrammar.ForStatementRejects statementOrdinary
          statementRejects expressionOrdinary expressionRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨forStatement_success_ordinary_sound statement expression
      statementOrdinary statementRejects expressionOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound
          expressionStrict,
    forStatement_reject_ordinary_sound statement expression
      statementOrdinary statementRejects expressionRejects expressionOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound
          expressionRejectSound expressionStrict⟩

/-- Re-export deterministic Core `for` outcomes. -/
theorem forStatement_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects)
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ForStatementOrdinaryParses statementOrdinary
        expressionOrdinary)
      (DeclarativeGrammar.ForStatementRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects) :=
  DeclarativeGrammar.forStatementDeterministicOutcomeSpec statementOutcomes
    expressionOutcomes

end Solcore.Syntax.Parser
