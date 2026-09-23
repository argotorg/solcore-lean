import Solcore.Syntax.DeclarativeFallbackDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact executable rejection of canonical contract fallback declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable fallback rejection occurs at its marker, parameter list,
or uncaptured required body.  Validation and entry modifiers cannot reject. -/
theorem fallbackDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : fallbackDecl input = .reject failure rejected) :
    DeclarativeGrammar.FallbackDeclRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold fallbackDecl at result
  cases markerResult : keyword .fallbackKw .contractMember input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .fallbackKw .contractMember
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .fallbackKw .contractMember
          markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .fallbackKw
        .contractMember markerResult
      cases parametersResult : ContractEntryInternals.entryParameters
          afterMarker with
      | invariant error => simp [parametersResult] at result
      | reject parametersFailure parametersRejected =>
          simp only [parametersResult] at result
          cases result
          exact .parametersRejected marker.span markerParsed
            (ContractEntryInternals.entryParameters_reject_ordinaryOutcome_sound
              parametersResult)
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          have parametersParsed :=
            ContractEntryInternals.entryParameters_success_ordinaryOutcome_sound
              parametersResult
          by_cases empty : parameters.elements.isEmpty
          · simp only [empty, if_true] at result
            have parameterless := List.nil_of_isEmpty empty
            cases modifiersResult :
                ContractEntryInternals.implicitPublicModifiers .fallbackKw
                  afterParameters with
            | invariant error => simp [modifiersResult] at result
            | reject modifiersFailure modifiersRejected =>
                exact False.elim
                  (ContractEntryInternals.implicitPublicModifiers_ne_reject
                    .fallbackKw modifiersResult)
            | ok payableMarker afterModifiers =>
                simp only [modifiersResult] at result
                have modifiersParsed :=
                  ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
                    .fallbackKw modifiersResult
                cases bodyResult : isolateBlock (block .require)
                    afterModifiers with
                | invariant error => simp [bodyResult] at result
                | ok body afterBody => simp [bodyResult, pure] at result
                | reject bodyFailure bodyRejected =>
                    simp only [bodyResult] at result
                    cases result
                    exact .bodyRejected marker.span markerParsed
                      parametersParsed (.empty parameterless) modifiersParsed
                      (isolatedCoreBlockPublic_reject_ordinary_sound .require
                        bodyResult)
          · simp only [empty, Bool.false_eq_true, if_false] at result
            have nonempty : parameters.elements ≠ [] := by
              intro parameterless
              rw [parameterless] at empty
              simp at empty
            simp only [emitDiagnostic, modifyState] at result
            cases modifiersResult :
                ContractEntryInternals.implicitPublicModifiers .fallbackKw
                  (afterParameters.emit {
                    span := parameters.span
                    kind := .constraintViolation
                      .fallbackRequiresNoParameters
                  }) with
            | invariant error => simp [modifiersResult] at result
            | reject modifiersFailure modifiersRejected =>
                exact False.elim
                  (ContractEntryInternals.implicitPublicModifiers_ne_reject
                    .fallbackKw modifiersResult)
            | ok payableMarker afterModifiers =>
                simp only [modifiersResult] at result
                have modifiersParsed :=
                  ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
                    .fallbackKw modifiersResult
                have normalizedModifiers :
                    DeclarativeGrammar.ContractEntryModifiersOrdinaryParses
                      afterParameters.declarativeRemainder payableMarker
                        afterModifiers.declarativeRemainder := by
                  simpa only [State.declarativeRemainder, State.emit] using
                    modifiersParsed
                cases bodyResult : isolateBlock (block .require)
                    afterModifiers with
                | invariant error => simp [bodyResult] at result
                | ok body afterBody => simp [bodyResult, pure] at result
                | reject bodyFailure bodyRejected =>
                    simp only [bodyResult] at result
                    cases result
                    exact .bodyRejected marker.span markerParsed
                      parametersParsed (.diagnosed nonempty)
                      normalizedModifiers
                      (isolatedCoreBlockPublic_reject_ordinary_sound .require
                        bodyResult)

end Solcore.Syntax.Parser
