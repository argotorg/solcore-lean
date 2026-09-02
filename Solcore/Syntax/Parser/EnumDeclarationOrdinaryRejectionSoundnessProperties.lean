import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.EnumBodyOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties

/-! Exact ordinary-rejection bridge for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present
      with ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

/-- Every rejected enum declaration records the first rejecting stage among
its marker, name, optional generic parameters, and body. -/
theorem enumDecl_reject_ordinaryOutcome_sound
    (deriveAttribute : Option DeriveAttribute)
    {input rejected : State} {failure : Failure}
    (result : enumDecl deriveAttribute input = .reject failure rejected) :
    DeclarativeGrammar.EnumDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold enumDecl at result
  cases markerResult : contextual .enum .topItem input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := contextual_reject_state_eq .enum .topItem
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .enum .topItem markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := contextual_success_exactTokenParses .enum .topItem
        markerResult
      cases nameResult : identifier .topItem afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (identifier_reject_sound .topItem nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .topItem nameResult
          cases parametersResult : optionalGenericParameters afterName with
          | invariant error => simp [parametersResult] at result
          | reject parametersFailure parametersRejected =>
              simp only [parametersResult] at result
              cases result
              exact .parametersRejected marker.span markerParsed nameParsed
                (optionalGenericParameters_reject_sound parametersResult)
          | ok parameters afterParameters =>
              simp only [parametersResult] at result
              have parametersParsed :=
                optionalGenericParameters_ordinaryOutcome_sound.1
                  parametersResult
              cases bodyResult : EnumInternals.enumBody afterParameters with
              | invariant error => simp [bodyResult] at result
              | reject bodyFailure bodyRejected =>
                  simp only [bodyResult] at result
                  cases result
                  exact .bodyRejected marker.span markerParsed nameParsed
                    parametersParsed
                    (EnumInternals.enumBody_reject_ordinaryOutcome_sound
                      bodyResult)
              | ok body output => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
