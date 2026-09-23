import Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties

/-! Ordinary success soundness for canonical contract fallback declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
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

/-- Every successful fallback preserves recovery-aware parameters, the exact
silent-or-diagnosed validation branch, fixed-order entry modifiers, and
balanced required-body recovery. -/
theorem fallbackDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : FallbackDecl}
    (result : fallbackDecl input = .ok declaration output) :
    DeclarativeGrammar.FallbackDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold fallbackDecl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  have markerParsed := keyword_success_exactTokenParses .fallbackKw
    .contractMember markerResult
  have parametersParsed :=
    ContractEntryInternals.entryParameters_success_ordinaryOutcome_sound
      parametersResult
  by_cases empty : parameters.elements.isEmpty
  · simp only [empty, if_true] at rest
    rcases bind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases bind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact .parsed marker.span markerParsed parametersParsed
      (.empty (List.nil_of_isEmpty empty))
      (ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
        .fallbackKw modifiersResult)
      (isolatedCoreBlockPublic_success_ordinary_sound .require bodyResult)
  · simp only [empty, Bool.false_eq_true, if_false] at rest
    rcases bind_ok_components rest with
      ⟨validation, afterValidation, validationResult, rest⟩
    rcases bind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases bind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    have nonempty : parameters.elements ≠ [] := by
      intro parameterless
      rw [parameterless] at empty
      simp at empty
    unfold emitDiagnostic modifyState at validationResult
    cases validationResult
    have modifiersParsed :=
      ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
        .fallbackKw modifiersResult
    have normalizedModifiers :
        DeclarativeGrammar.ContractEntryModifiersOrdinaryParses
          afterParameters.declarativeRemainder payableMarker
            afterModifiers.declarativeRemainder := by
      simpa only [State.declarativeRemainder, State.emit] using
        modifiersParsed
    exact .parsed marker.span markerParsed parametersParsed
      (.diagnosed nonempty)
      normalizedModifiers
      (isolatedCoreBlockPublic_success_ordinary_sound .require bodyResult)

end Solcore.Syntax.Parser
