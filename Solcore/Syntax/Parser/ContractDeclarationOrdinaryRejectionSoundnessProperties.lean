import Solcore.Syntax.DeclarativeContractDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.ContractBodyOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact broad ordinary rejection for complete contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable contract-declaration rejection occurs at the first of
its marker, name, optional generic parameters, or recovery-aware body. -/
theorem contractDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : contractDecl input = .reject failure rejected) :
    DeclarativeGrammar.ContractDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold contractDecl at result
  cases markerResult : keyword .contractKw .topItem input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .contractKw .topItem
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .contractKw .topItem markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .contractKw
        .topItem markerResult
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
          cases genericsResult : optionalGenericParameters afterName with
          | invariant error => simp [genericsResult] at result
          | reject genericsFailure genericsRejected =>
              simp only [genericsResult] at result
              cases result
              exact .genericsRejected marker.span markerParsed nameParsed
                (optionalGenericParameters_ordinaryOutcome_sound.2
                  genericsResult)
          | ok genericParameters afterGenerics =>
              simp only [genericsResult] at result
              have genericsParsed :=
                optionalGenericParameters_ordinaryOutcome_sound.1
                  genericsResult
              cases bodyResult : ContractInternals.contractBody afterGenerics with
              | invariant error => simp [bodyResult] at result
              | reject bodyFailure bodyRejected =>
                  simp only [bodyResult] at result
                  cases result
                  exact .bodyRejected marker.span markerParsed nameParsed
                    genericsParsed
                    (ContractInternals.contractBody_reject_ordinaryOutcome_sound
                      bodyResult)
              | ok body output => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser
