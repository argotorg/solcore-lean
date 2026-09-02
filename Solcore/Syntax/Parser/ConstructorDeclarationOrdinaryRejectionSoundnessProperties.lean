import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.ContractEntryModifierOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact executable rejection of canonical contract constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable constructor rejection occurs at its marker, parameter
list, or uncaptured required body.  Entry modifiers themselves cannot reject. -/
theorem constructorDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : constructorDecl input = .reject failure rejected) :
    DeclarativeGrammar.ConstructorDeclRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold constructorDecl at result
  cases markerResult : keyword .constructorKw .contractMember input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have rejectedEq := keyword_reject_state_eq .constructorKw
        .contractMember markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (keyword_reject_tokenKindAbsentAt .constructorKw .contractMember
          markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := keyword_success_exactTokenParses .constructorKw
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
          cases modifiersResult :
              ContractEntryInternals.implicitPublicModifiers .constructorKw
                afterParameters with
          | invariant error => simp [modifiersResult] at result
          | reject modifiersFailure modifiersRejected =>
              exact False.elim
                (ContractEntryInternals.implicitPublicModifiers_ne_reject
                  .constructorKw modifiersResult)
          | ok payableMarker afterModifiers =>
              simp only [modifiersResult] at result
              have modifiersParsed :=
                ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
                  .constructorKw modifiersResult
              cases bodyResult : isolateBlock (block .require) afterModifiers with
              | invariant error => simp [bodyResult] at result
              | ok body afterBody => simp [bodyResult, pure] at result
              | reject bodyFailure bodyRejected =>
                  simp only [bodyResult] at result
                  cases result
                  exact .bodyRejected marker.span markerParsed
                    parametersParsed modifiersParsed
                    (isolatedCoreBlockPublic_reject_ordinary_sound .require
                      bodyResult)

end Solcore.Syntax.Parser
