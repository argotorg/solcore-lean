import Solcore.Syntax.DeclarativeContractDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.ContractBodyOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties

/-! Broad ordinary-success soundness for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable contract declaration success records its exact marker,
name, optional generic parameters, broad recovery-aware body, constructed AST,
covered span, and final remainder without a diagnostic-free premise. -/
theorem contractDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ContractDecl}
    (result : contractDecl input = .ok declaration output) :
    DeclarativeGrammar.ContractDeclOrdinaryParses input.declarativeRemainder
      declaration output.declarativeRemainder := by
  unfold contractDecl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .contractKw .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (optionalGenericParameters_ordinaryOutcome_sound.1 genericsResult)
    (ContractInternals.contractBody_success_ordinaryOutcome_sound bodyResult)

end Solcore.Syntax.Parser
