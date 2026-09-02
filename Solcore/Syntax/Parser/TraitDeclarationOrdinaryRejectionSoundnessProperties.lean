import Solcore.Syntax.DeclarativeTraitDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TraitBodyOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties

/-! Exact broad ordinary rejection for complete trait declarations. -/

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

/-- Every executable trait-declaration rejection records its first rejecting
stage among marker, name, required generics, where clause, and broad body. -/
theorem traitDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : traitDecl input = .reject failure rejected) :
    DeclarativeGrammar.TraitDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold traitDecl at result
  cases markerResult : contextual .trait .topItem input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := contextual_reject_state_eq .trait .topItem
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .trait .topItem markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := contextual_success_exactTokenParses .trait .topItem
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
          cases genericsResult : genericParameters afterName with
          | invariant error => simp [genericsResult] at result
          | reject genericsFailure genericsRejected =>
              simp only [genericsResult] at result
              cases result
              exact .genericsRejected marker.span markerParsed nameParsed
                (genericParameters_ordinaryOutcome_sound.2 genericsResult)
          | ok genericParameters afterGenerics =>
              simp only [genericsResult] at result
              have genericsParsed := genericParameters_ordinaryOutcome_sound.1
                genericsResult
              cases whereResult : whereClause afterGenerics with
              | invariant error => simp [whereResult] at result
              | reject whereFailure whereRejected =>
                  simp only [whereResult] at result
                  cases result
                  exact .whereRejected marker.span markerParsed nameParsed
                    genericsParsed (whereClause_ordinaryOutcome_sound.2
                      whereResult)
              | ok parsedWhere afterWhere =>
                  simp only [whereResult] at result
                  have whereParsed := whereClause_ordinaryOutcome_sound.1
                    whereResult
                  cases bodyResult : TraitInternals.traitBody afterWhere with
                  | invariant error => simp [bodyResult] at result
                  | reject bodyFailure bodyRejected =>
                      simp only [bodyResult] at result
                      cases result
                      exact .bodyRejected marker.span markerParsed nameParsed
                        genericsParsed whereParsed
                        (TraitInternals.traitBody_reject_ordinaryOutcome_sound
                          bodyResult)
                  | ok body output => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
