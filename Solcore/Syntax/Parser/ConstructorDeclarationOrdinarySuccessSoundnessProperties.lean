import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Ordinary success soundness for canonical contract constructors. -/

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

/-- Every successful constructor follows its exact marker, recovery-aware
parameters, ordinary modifiers, and isolated required-body grammar. -/
theorem constructorDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ConstructorDecl}
    (result : constructorDecl input = .ok declaration output) :
    DeclarativeGrammar.ConstructorDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold constructorDecl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .constructorKw .contractMember
      markerResult)
    (ContractEntryInternals.entryParameters_success_ordinaryOutcome_sound
      parametersResult)
    (ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
      .constructorKw modifiersResult)
    (isolatedCoreBlockPublic_success_ordinary_sound .require bodyResult)

end Solcore.Syntax.Parser
