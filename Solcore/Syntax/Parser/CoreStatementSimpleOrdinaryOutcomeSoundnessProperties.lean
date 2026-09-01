import Solcore.Syntax.DeclarativeCoreStatementSimpleCompleteOutcomeProperties
import Solcore.Syntax.Parser.CoreStatementSimpleOrdinaryRejectionSoundnessProperties

/-! Packaged ordinary outcomes for canonical Core `let` and `return`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package executable Core `let` success and exact rejection. -/
theorem letStatement_ordinaryOutcome_sound
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
    (∀ {input output : State} {statement : Statement},
      letStatement expression input = .ok statement output →
        DeclarativeGrammar.LetStatementOrdinaryParses expressionOrdinary
          input.declarativeRemainder statement output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      letStatement expression input = .reject failure rejected →
        DeclarativeGrammar.LetStatementRejects expressionOrdinary
          expressionRejects DeclarativeGrammar.TypeExprRejects
            input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨letStatement_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    letStatement_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic Core `let` outcomes with the fixed public Core
type outcome. -/
theorem letStatement_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LetStatementOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.LetStatementRejects expressionOrdinary
        expressionRejects DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.letStatementDeterministicOutcomeSpec expressionOutcomes
    DeclarativeGrammar.typeExprDeterministicOutcomeSpec

/-- Package executable Core `return` success and exact rejection. -/
theorem returnStatement_ordinaryOutcome_sound
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
    (∀ {input output : State} {statement : Statement},
      returnStatement expression input = .ok statement output →
        DeclarativeGrammar.ReturnStatementOrdinaryParses expressionOrdinary
          input.declarativeRemainder statement output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      returnStatement expression input = .reject failure rejected →
        DeclarativeGrammar.ReturnStatementRejects expressionOrdinary
          expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨returnStatement_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound,
    returnStatement_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic Core `return` outcomes. -/
theorem returnStatement_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ReturnStatementOrdinaryParses expressionOrdinary)
      (DeclarativeGrammar.ReturnStatementRejects expressionOrdinary
        expressionRejects) :=
  DeclarativeGrammar.returnStatementDeterministicOutcomeSpec
    expressionOutcomes

end Solcore.Syntax.Parser
