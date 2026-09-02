import Solcore.Syntax.DeclarativeImplDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplBodyOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplDefaultMarkerOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImplHeadArgumentsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties

/-! Exact broad ordinary rejection for implementation declarations. -/

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

/-- Every executable implementation rejection occurs after its infallible
default prefix at the first of marker, generics, name, arguments, where, or
broad body. -/
theorem implDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : implDecl input = .reject failure rejected) :
    DeclarativeGrammar.ImplDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold implDecl at result
  cases defaultResult : ImplInternals.implDefaultMarker input with
  | invariant error => simp [bind, defaultResult] at result
  | reject defaultFailure defaultRejected =>
      exact False.elim
        (ImplInternals.implDefaultMarker_reject_ordinaryOutcome_sound
          defaultResult)
  | ok defaultMarker afterDefault =>
      simp only [bind, defaultResult] at result
      have defaultParsed :=
        ImplInternals.implDefaultMarker_success_ordinaryOutcome_sound
          defaultResult
      unfold ImplInternals.implDeclAfterDefault at result
      cases markerResult : contextual .impl .topItem afterDefault with
      | invariant error => simp [bind, markerResult] at result
      | reject markerFailure markerRejected =>
          have markerRejectedEq := contextual_reject_state_eq .impl .topItem
            markerResult
          subst markerRejected
          simp only [bind, markerResult] at result
          cases result
          exact .markerMissing defaultParsed
            (contextual_reject_tokenKindAbsentAt .impl .topItem markerResult)
      | ok marker afterMarker =>
          simp only [bind, markerResult] at result
          have markerParsed := contextual_success_exactTokenParses .impl
            .topItem markerResult
          cases genericsResult : optionalGenericParameters afterMarker with
          | invariant error => simp [genericsResult] at result
          | reject genericsFailure genericsRejected =>
              simp only [genericsResult] at result
              cases result
              exact .genericsRejected defaultParsed marker.span markerParsed
                (optionalGenericParameters_ordinaryOutcome_sound.2
                  genericsResult)
          | ok genericParameters afterGenerics =>
              simp only [genericsResult] at result
              have genericsParsed :=
                optionalGenericParameters_ordinaryOutcome_sound.1
                  genericsResult
              cases nameResult : identifier .topItem afterGenerics with
              | invariant error => simp [nameResult] at result
              | reject nameFailure nameRejected =>
                  simp only [nameResult] at result
                  cases result
                  exact .nameRejected defaultParsed marker.span markerParsed
                    genericsParsed
                    (identifier_reject_sound .topItem nameResult)
              | ok traitName afterName =>
                  simp only [nameResult] at result
                  have nameParsed := identifier_success_sound .topItem
                    nameResult
                  cases valuesResult : delimited .less .greater false typeExpr
                      .typeExpr .topLevel afterName with
                  | invariant error => simp [valuesResult] at result
                  | reject valuesFailure valuesRejected =>
                      simp only [valuesResult] at result
                      cases result
                      exact .argumentsRejected defaultParsed marker.span
                        markerParsed genericsParsed nameParsed
                        (ImplInternals.implHeadArguments_reject_ordinaryOutcome_sound
                            valuesResult)
                  | ok values afterValues =>
                      simp only [valuesResult] at result
                      cases argumentsResult :
                          ImplInternals.requireImplArguments values afterValues
                          with
                      | invariant error => simp [argumentsResult] at result
                      | reject argumentsFailure argumentsRejected =>
                          exact False.elim
                            (ImplInternals.requireImplArguments_ne_reject
                              values afterValues argumentsRejected
                                argumentsFailure argumentsResult)
                      | ok headArguments afterArguments =>
                          simp only [argumentsResult] at result
                          have argumentsParsed :=
                            ImplInternals.implHeadArguments_success_ordinaryOutcome_sound
                                valuesResult argumentsResult
                          cases whereResult : whereClause afterArguments with
                          | invariant error => simp [whereResult] at result
                          | reject whereFailure whereRejected =>
                              simp only [whereResult] at result
                              cases result
                              exact .whereRejected defaultParsed marker.span
                                markerParsed genericsParsed nameParsed
                                argumentsParsed
                                (whereClause_ordinaryOutcome_sound.2
                                  whereResult)
                          | ok parsedWhere afterWhere =>
                              simp only [whereResult] at result
                              have whereParsed :=
                                whereClause_ordinaryOutcome_sound.1 whereResult
                              cases bodyResult : ImplInternals.implBody
                                  afterWhere with
                              | invariant error => simp [bodyResult] at result
                              | reject bodyFailure bodyRejected =>
                                  simp only [bodyResult] at result
                                  cases result
                                  exact .bodyRejected defaultParsed marker.span
                                    markerParsed genericsParsed nameParsed
                                    argumentsParsed whereParsed
                                    (ImplInternals.implBody_reject_ordinaryOutcome_sound
                                        bodyResult)
                              | ok body output =>
                                  simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
