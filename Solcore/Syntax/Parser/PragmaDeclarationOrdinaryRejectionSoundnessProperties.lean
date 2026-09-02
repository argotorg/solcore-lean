import Solcore.Syntax.DeclarativePragmaOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.PragmaItemsOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.RawIdentifierOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties

/-! Exact executable ordinary rejection for complete pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable pragma rejection records the exact first failing keyword,
raw name, checked item scan, or final semicolon stage. -/
theorem pragmaDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : pragmaDecl input = .reject failure rejected) :
    DeclarativeGrammar.PragmaDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .pragmaKw .pragmaDecl
        keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt .pragmaKw .pragmaDecl
          keywordResult)
  | ok pragmaKeyword afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordParsed := keyword_success_exactTokenParses .pragmaKw
        .pragmaDecl keywordResult
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected pragmaKeyword.span keywordParsed
            (rawIdentifier_reject_ordinaryOutcome_sound .pragmaDecl
              nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := rawIdentifier_success_ordinaryOutcome_sound
            .pragmaDecl nameResult
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject itemsFailure itemsRejected =>
              simp only [itemsResult] at result
              cases result
              exact .itemsRejected pragmaKeyword.span keywordParsed
                nameParsed
                (PragmaInternals.pragmaItems_reject_ordinaryOutcome_sound
                  itemsResult)
          | ok items afterItems =>
              simp only [itemsResult] at result
              have itemsParsed :=
                PragmaInternals.pragmaItems_success_ordinaryOutcome_sound
                  itemsResult
              cases semicolonResult : symbol .semicolon .pragmaDecl
                  afterItems with
              | invariant error => simp [semicolonResult] at result
              | ok semicolon output => simp [semicolonResult, pure] at result
              | reject semicolonFailure semicolonRejected =>
                  have rejectedEq := symbol_reject_state_eq .semicolon
                    .pragmaDecl semicolonResult
                  subst semicolonRejected
                  simp only [semicolonResult] at result
                  cases result
                  exact .semicolonMissing pragmaKeyword.span keywordParsed
                    nameParsed itemsParsed
                    (symbol_reject_tokenKindAbsentAt .semicolon .pragmaDecl
                      semicolonResult)

end Solcore.Syntax.Parser
