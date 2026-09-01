import Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionAtomLeafSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionNameOutcomeSoundnessProperties

/-! Executable ordinary outcomes for a Core identifier expression leaf. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Identifier-expression rejection is exactly rejection of its wrapped
Boolean-first expression name. -/
theorem identifierExpression_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : identifierExpression input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierExpressionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold identifierExpression at result
  cases nameResult : expressionName input with
  | invariant error => simp [bind, nameResult] at result
  | ok name afterName => simp [bind, nameResult, pure] at result
  | reject nameFailure nameRejected =>
      simp only [bind, nameResult] at result
      cases result
      exact .nameRejected (expressionName_reject_ordinary_sound nameResult)

/-- Package unconditional identifier-expression success and rejection. -/
theorem identifierExpression_ordinaryOutcome_sound :
    (∀ {input output : State} {expression : Expr},
      identifierExpression input = .ok expression output →
        DeclarativeGrammar.IdentifierExpressionOrdinaryParses
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      identifierExpression input = .reject failure rejected →
        DeclarativeGrammar.IdentifierExpressionRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨identifierExpression_success_sound,
    identifierExpression_reject_ordinary_sound⟩

/-- Re-export the deterministic identifier-expression outcome at its
executable boundary. -/
theorem identifierExpression_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.IdentifierExpressionOrdinaryParses
      DeclarativeGrammar.IdentifierExpressionRejects :=
  DeclarativeGrammar.identifierExpressionDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ExpressionAtomInternals
