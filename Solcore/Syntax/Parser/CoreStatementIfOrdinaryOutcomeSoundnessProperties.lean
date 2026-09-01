import Solcore.Syntax.Parser.CoreStatementIfOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.DeclarativeCoreStatementIfOutcomeProperties

/-! Packaged executable ordinary outcomes for canonical Core `if`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable Core `if` success and exact rejection. -/
theorem ifStatement_ordinaryOutcome_sound
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
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {value : Statement},
      ifStatement statement expression input = .ok value output →
        DeclarativeGrammar.IfStatementOrdinaryParses expressionOrdinary
          statementOrdinary input.declarativeRemainder value
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ifStatement statement expression input = .reject failure rejected →
        DeclarativeGrammar.IfStatementRejects expressionOrdinary
          expressionRejects statementOrdinary statementRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨ifStatement_success_ordinary_sound statement expression statementOrdinary
      statementRejects expressionOrdinary statementSuccessSound
        statementRejectSound expressionSuccessSound,
    ifStatement_reject_ordinary_sound statement expression statementOrdinary
      statementRejects expressionRejects expressionOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound
          expressionRejectSound⟩

/-- Re-export deterministic Core `if` outcomes. -/
theorem ifStatement_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.IfStatementOrdinaryParses expressionOrdinary
        statementOrdinary)
      (DeclarativeGrammar.IfStatementRejects expressionOrdinary
        expressionRejects statementOrdinary statementRejects) :=
  DeclarativeGrammar.ifStatementDeterministicOutcomeSpec expressionOutcomes
    statementOutcomes

end Solcore.Syntax.Parser
