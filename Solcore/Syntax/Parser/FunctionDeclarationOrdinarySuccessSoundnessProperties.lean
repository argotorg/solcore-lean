import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Function
import Solcore.Syntax.Parser.FunctionSignatureOrdinarySuccessSoundnessProperties

/-! Ordinary success soundness for complete named-function declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Every successful complete function declaration follows the recovery-aware
ordinary signature and isolated public Core block grammar. -/
theorem functionDecl_success_ordinaryOutcome_sound
    (location : FunctionLocation) {input output : State}
    {declaration : FunctionDecl}
    (result : functionDecl location input = .ok declaration output) :
    DeclarativeGrammar.FunctionDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold functionDecl at result
  rcases bind_ok_components result with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed
    (functionSignature_success_ordinaryOutcome_sound location signatureResult)
    (isolatedCoreBlockPublic_success_ordinary_sound .allow bodyResult)

end Solcore.Syntax.Parser
