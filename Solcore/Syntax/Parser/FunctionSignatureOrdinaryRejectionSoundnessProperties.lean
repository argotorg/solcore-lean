import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.FunctionModifierSoundnessProperties
import Solcore.Syntax.Parser.FunctionParametersOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ReturnClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact first-stage rejection of executable function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem optionalFunctionModifier_ne_reject
    (keywordValue : HardKeyword) {input rejected : State} {failure : Failure}
    (result : optionalFunctionModifier keywordValue input =
      .reject failure rejected) : False := by
  unfold optionalFunctionModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input keywordValue
  · rcases keyword_eq_ok_of_isKeyword_eq_true keywordValue .parameter
        present with ⟨marker, markerResult⟩
    simp [present, markerResult, pure] at result
  · have absent : isKeyword input keywordValue = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

private theorem functionModifiers_ne_reject
    (location : FunctionLocation) {input rejected : State}
    {failure : Failure}
    (result : functionModifiers location input = .reject failure rejected) :
    False := by
  unfold functionModifiers at result
  cases publicResult : optionalFunctionModifier .publicKw input with
  | invariant error => simp [bind, publicResult] at result
  | reject publicFailure publicRejected =>
      exact optionalFunctionModifier_ne_reject .publicKw publicResult
  | ok publicMarker afterPublic =>
      simp only [bind, publicResult] at result
      cases payableResult : optionalFunctionModifier .payableKw afterPublic with
      | invariant error => simp [payableResult] at result
      | reject payableFailure payableRejected =>
          exact optionalFunctionModifier_ne_reject .payableKw payableResult
      | ok payableMarker afterPayable =>
          simp only [payableResult] at result
          exact finishFunctionModifiers_ne_reject location publicMarker
            payableMarker afterPayable rejected failure result

/-- Every executable signature rejection records the exact first rejecting
structural stage; modifier parsing itself cannot reject. -/
theorem functionSignature_reject_ordinaryOutcome_sound
    (location : FunctionLocation) {input rejected : State}
    {failure : Failure}
    (result : functionSignature location input = .reject failure rejected) :
    DeclarativeGrammar.FunctionSignatureRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold functionSignature at result
  cases keywordResult : keyword .functionKw .topItem input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .functionKw .topItem
        keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt .functionKw .topItem keywordResult)
  | ok functionToken afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordParsed := keyword_success_exactTokenParses .functionKw
        .topItem keywordResult
      cases nameResult : identifier .topItem afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected functionToken.span keywordParsed
            (identifier_reject_sound .topItem nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .topItem nameResult
          cases genericsResult : optionalGenericParameters afterName with
          | invariant error => simp [genericsResult] at result
          | reject genericsFailure genericsRejected =>
              simp only [genericsResult] at result
              cases result
              exact .genericsRejected functionToken.span keywordParsed
                nameParsed
                (optionalGenericParameters_reject_sound genericsResult)
          | ok genericParameters afterGenerics =>
              simp only [genericsResult] at result
              have genericsParsed :=
                optionalGenericParameters_ordinaryOutcome_sound.1
                  genericsResult
              cases parametersResult : functionParameters afterGenerics with
              | invariant error => simp [parametersResult] at result
              | reject parametersFailure parametersRejected =>
                  simp only [parametersResult] at result
                  cases result
                  exact .parametersRejected functionToken.span keywordParsed
                    nameParsed genericsParsed
                    (functionParameters_reject_ordinaryOutcome_sound
                      parametersResult)
              | ok parameters afterParameters =>
                  simp only [parametersResult] at result
                  have parametersParsed :=
                    functionParameters_success_ordinaryOutcome_sound
                      parametersResult
                  cases modifiersResult : functionModifiers location
                      afterParameters with
                  | invariant error => simp [modifiersResult] at result
                  | reject modifiersFailure modifiersRejected =>
                      exact False.elim
                        (functionModifiers_ne_reject location modifiersResult)
                  | ok modifiers afterModifiers =>
                      simp only [modifiersResult] at result
                      have modifiersParsed := functionModifiers_success_sound
                        location modifiersResult
                      cases returnsResult : returnClause afterModifiers with
                      | invariant error => simp [returnsResult] at result
                      | reject returnsFailure returnsRejected =>
                          simp only [returnsResult] at result
                          cases result
                          exact .returnsRejected functionToken.span
                            keywordParsed nameParsed genericsParsed
                            parametersParsed modifiersParsed
                            (returnClause_reject_sound returnsResult)
                      | ok returnsClause afterReturns =>
                          simp only [returnsResult] at result
                          have returnsParsed :=
                            returnClause_ordinaryOutcome_sound.1 returnsResult
                          cases whereResult : whereClause afterReturns with
                          | invariant error => simp [whereResult] at result
                          | ok whereClause afterWhere =>
                              simp [whereResult, pure] at result
                          | reject whereFailure whereRejected =>
                              simp only [whereResult] at result
                              cases result
                              exact .whereRejected functionToken.span
                                keywordParsed nameParsed genericsParsed
                                parametersParsed modifiersParsed returnsParsed
                                (whereClause_reject_sound whereResult)

end Solcore.Syntax.Parser
