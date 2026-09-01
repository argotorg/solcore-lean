import Solcore.Syntax.DeclarativeCoreStatementLayerOutcomeProperties
import Solcore.Syntax.Parser.CoreStatementLayerOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreStatementLayerOrdinarySuccessSoundnessProperties

/-! Packaged ordinary outcomes for the ordered Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Package executable success and exact rejection for one Core statement
layer with the same recursive callbacks. -/
theorem statementLayer_ordinaryOutcome_sound
    (nestedStatement : Parser Statement) (expression : Parser Expr)
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
      nestedStatement input = .ok value output → statementOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (statementRejectSound : ∀ {input rejected : State} {failure : Failure},
      nestedStatement input = .reject failure rejected → statementRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionStrict : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → input.cursor < output.cursor)
    (patternSuccessSound : ∀ {input output : State} {value : Pattern},
      pattern input = .ok value output → patternOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (patternRejectSound : ∀ {input rejected : State} {failure : Failure},
      pattern input = .reject failure rejected → patternRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {value : Statement},
      statementLayer nestedStatement expression pattern input =
          .ok value output →
        DeclarativeGrammar.StatementLayerOrdinaryParses statementOrdinary
          statementRejects expressionOrdinary expressionRejects
            patternOrdinary patternRejects input.declarativeRemainder value
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      statementLayer nestedStatement expression pattern input =
          .reject failure rejected →
        DeclarativeGrammar.StatementLayerRejects statementOrdinary
          statementRejects expressionOrdinary expressionRejects
            patternOrdinary patternRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨statementLayer_success_ordinary_sound nestedStatement expression pattern
      statementOrdinary statementRejects expressionOrdinary expressionRejects
        patternOrdinary patternRejects statementSuccessSound
          statementRejectSound expressionSuccessSound expressionRejectSound
            expressionWindow expressionStrict patternSuccessSound
              patternRejectSound,
    statementLayer_reject_ordinary_sound nestedStatement expression pattern
      statementOrdinary statementRejects expressionRejects patternRejects
        expressionOrdinary patternOrdinary statementSuccessSound
          statementRejectSound expressionSuccessSound expressionRejectSound
            expressionWindow expressionStrict patternSuccessSound
              patternRejectSound⟩

/-- Re-export the deterministic contract under the executable bridge name. -/
theorem statementLayer_ordinaryOutcomeSpec
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
      (DeclarativeGrammar.StatementLayerOrdinaryParses statementOrdinary
        statementRejects expressionOrdinary expressionRejects patternOrdinary
          patternRejects)
      (DeclarativeGrammar.StatementLayerRejects statementOrdinary
        statementRejects expressionOrdinary expressionRejects patternOrdinary
          patternRejects) :=
  DeclarativeGrammar.statementLayerDeterministicOutcomeSpec statementOutcomes
    expressionOutcomes patternOutcomes

end Solcore.Syntax.Parser.TermInternals
