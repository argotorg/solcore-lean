import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.TypeAliasParametersOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasValueOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact executable rejection for complete transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable type-alias rejection records its exact first failing
keyword, name, parameter list, equals token, value, or semicolon stage. -/
theorem typeAlias_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : typeAlias input = .reject failure rejected) :
    DeclarativeGrammar.TypeAliasDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold typeAlias at result
  cases keywordResult : keyword .typeKw .typeAlias input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .typeKw .typeAlias
        keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt .typeKw .typeAlias keywordResult)
  | ok typeKeyword afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordParsed := keyword_success_exactTokenParses .typeKw
        .typeAlias keywordResult
      cases nameResult : identifier .typeAlias afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected typeKeyword.span keywordParsed
            (identifier_reject_sound .typeAlias nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .typeAlias nameResult
          cases parametersResult : parseTypeAliasParameters afterName with
          | invariant error => simp [parametersResult] at result
          | reject parametersFailure parametersRejected =>
              simp only [parametersResult] at result
              cases result
              exact .parametersRejected typeKeyword.span keywordParsed
                nameParsed
                (parseTypeAliasParameters_reject_ordinaryOutcome_sound
                  parametersResult)
          | ok parameters afterParameters =>
              simp only [parametersResult] at result
              have parametersParsed :=
                parseTypeAliasParameters_success_ordinaryOutcome_sound
                  parametersResult
              cases equalResult : symbol .equal .typeAlias afterParameters with
              | invariant error => simp [equalResult] at result
              | reject equalFailure equalRejected =>
                  have rejectedEq := symbol_reject_state_eq .equal .typeAlias
                    equalResult
                  subst equalRejected
                  simp only [equalResult] at result
                  cases result
                  exact .equalMissing typeKeyword.span keywordParsed
                    nameParsed parametersParsed
                    (symbol_reject_tokenKindAbsentAt .equal .typeAlias
                      equalResult)
              | ok equal afterEqual =>
                  simp only [equalResult] at result
                  have equalParsed := symbol_success_exactTokenParses .equal
                    .typeAlias equalResult
                  cases valueResult : TypeAliasInternals.parseAliasValue
                      afterEqual with
                  | invariant error => simp [valueResult] at result
                  | reject valueFailure valueRejected =>
                      simp only [valueResult] at result
                      cases result
                      exact .valueRejected typeKeyword.span equal.span
                        keywordParsed nameParsed parametersParsed equalParsed
                        (TypeAliasInternals.parseAliasValue_reject_ordinaryOutcome_sound
                          valueResult)
                  | ok value afterValue =>
                      simp only [valueResult] at result
                      have valueParsed :=
                        TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound
                          valueResult
                      cases semicolonResult : symbol .semicolon .typeAlias
                          afterValue with
                      | invariant error => simp [semicolonResult] at result
                      | ok semicolon output =>
                          simp [semicolonResult, pure] at result
                      | reject semicolonFailure semicolonRejected =>
                          have rejectedEq := symbol_reject_state_eq .semicolon
                            .typeAlias semicolonResult
                          subst semicolonRejected
                          simp only [semicolonResult] at result
                          cases result
                          exact .semicolonMissing typeKeyword.span equal.span
                            keywordParsed nameParsed parametersParsed
                            equalParsed valueParsed
                            (symbol_reject_tokenKindAbsentAt .semicolon
                              .typeAlias semicolonResult)

end Solcore.Syntax.Parser
