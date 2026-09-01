import Solcore.Syntax.Parser.CoreMatchStatementOrdinaryRejectionSoundnessProperties

/-! Packaged executable ordinary outcomes for complete Core matches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package complete Core match success and exact rejection. -/
theorem matchStatement_ordinaryOutcome_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (patternRejects : DeclarativeGrammar.Remainder →
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
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {value : Statement},
      matchStatement statement expression pattern input = .ok value output →
        DeclarativeGrammar.MatchStatementOrdinaryParses statementOrdinary
          expressionOrdinary patternOrdinary input.declarativeRemainder value
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      matchStatement statement expression pattern input =
          .reject failure rejected →
        DeclarativeGrammar.MatchStatementRejects statementOrdinary
          statementRejects expressionOrdinary expressionRejects
            patternOrdinary patternRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨matchStatement_success_ordinary_sound statement expression pattern
      statementOrdinary statementRejects expressionOrdinary patternOrdinary
        statementSuccessSound statementRejectSound expressionSuccessSound
          expressionWindow patternSuccessSound,
    matchStatement_reject_ordinary_sound statement expression pattern
      statementOrdinary statementRejects expressionOrdinary expressionRejects
        patternOrdinary patternRejects statementSuccessSound
          statementRejectSound expressionSuccessSound expressionRejectSound
            expressionWindow patternSuccessSound patternRejectSound⟩

/-- Re-export deterministic complete Core match outcomes. -/
theorem matchStatement_ordinaryOutcomeSpec
    {statementOrdinary : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop}
    {statementRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {patternOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop}
    {patternRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (statementOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      statementOrdinary statementRejects)
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects)
    (patternOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      patternOrdinary patternRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.MatchStatementOrdinaryParses statementOrdinary
        expressionOrdinary patternOrdinary)
      (DeclarativeGrammar.MatchStatementRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects
          patternOrdinary patternRejects) :=
  DeclarativeGrammar.matchStatementDeterministicOutcomeSpec
    statementOutcomes expressionOutcomes patternOutcomes

end Solcore.Syntax.Parser
