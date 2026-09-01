import Solcore.Syntax.Parser.CoreLambdaParameterRecoveryOrdinarySoundnessProperties
import Solcore.Syntax.Parser.ParameterRecoveryTotalityProperties

/-! Complete ordinary outcomes of standalone parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FunctionParameterInternals

private theorem recoveryRejects_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.FunctionParameterRecoveryRejects
      input.declarativeRemainder input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.FunctionParameterRecoveryRejects.missingToken
      inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- Every complete executable recovery rejection is the unavailable first
token and preserves the full declarative remainder. -/
theorem recoverParameter_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : recoverParameter input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverParameter at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      exact recoveryRejects_of_advance?_eq_none input advanced
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverParameterAux_production_exists_ok token.span token.span next
        with ⟨parameter, output, success⟩
      rw [success] at result
      contradiction

/-- Package function-recovery success and rejection reflection. -/
theorem recoverParameter_ordinaryOutcome_sound :
    (∀ {input output : State} {parameter : FunctionParameter},
      recoverParameter input = .ok parameter output →
        DeclarativeGrammar.FunctionParameterRecoveryParses
          input.declarativeRemainder parameter output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverParameter input = .reject failure rejected →
        DeclarativeGrammar.FunctionParameterRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverParameter_success_ordinary_sound,
    recoverParameter_reject_ordinary_sound⟩

end FunctionParameterInternals

namespace LambdaParameterInternals

/-- Lambda recovery propagates the exact unavailable-first-token rejection. -/
theorem recoverLambdaParameter_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : recoverLambdaParameter input = .reject failure rejected) :
    DeclarativeGrammar.LambdaParameterRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverLambdaParameter at result
  cases recoveredResult : FunctionParameterInternals.recoverParameter input with
  | invariant error => simp [recoveredResult] at result
  | ok recovered output => simp [recoveredResult] at result
  | reject recoveryFailure recoveryRejected =>
      simp only [recoveredResult] at result
      cases result
      exact FunctionParameterInternals.recoverParameter_reject_ordinary_sound
        recoveredResult

/-- Package lambda-recovery success and rejection reflection. -/
theorem recoverLambdaParameter_ordinaryOutcome_sound :
    (∀ {input output : State} {parameter : LambdaParameter},
      recoverLambdaParameter input = .ok parameter output →
        DeclarativeGrammar.LambdaParameterRecoveryParses
          input.declarativeRemainder parameter output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverLambdaParameter input = .reject failure rejected →
        DeclarativeGrammar.LambdaParameterRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverLambdaParameter_success_ordinary_sound,
    recoverLambdaParameter_reject_ordinary_sound⟩

/-- Re-export deterministic standalone lambda-recovery outcomes. -/
theorem recoverLambdaParameter_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.LambdaParameterRecoveryParses
      DeclarativeGrammar.LambdaParameterRecoveryRejects :=
  DeclarativeGrammar.lambdaParameterRecoveryDeterministicOutcomeSpec

end LambdaParameterInternals
end Solcore.Syntax.Parser
