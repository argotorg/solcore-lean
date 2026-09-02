import Solcore.Syntax.DeclarativeExportDeclOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.LocalExportOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PathExportOrdinaryOutcomeSoundnessProperties

/-! Exact executable rejection reflection for complete export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem exportKeyword_reject_tokenKindAbsentAt
    {input rejected : State} {failure : Failure}
    (result : keyword .exportKw .exportDecl input =
      .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword .exportKw) := by
  by_cases present : isKeyword input .exportKw = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true .exportKw .exportDecl present
        with ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact keywordAbsentAt_of_isKeyword_eq_false .exportKw
      (Bool.eq_false_iff.mpr present)

private theorem exportKeyword_reject_state_eq
    {input rejected : State} {failure : Failure}
    (result : keyword .exportKw .exportDecl input =
      .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.keyword .exportKw) .exportDecl
    (· == .keyword .exportKw) result

private theorem exportDeclLeftBracePresentAt_of_isSymbol_eq_true
    {input : State} (present : isSymbol input .leftBrace = true) :
    DeclarativeGrammar.ExportDeclLeftBracePresentAt
      input.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftBrace .exportDecl present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses .leftBrace .exportDecl parsed).1⟩

/-- Every executable complete-export rejection records the exact missing
keyword or the uniquely selected local/path payload rejection. -/
theorem exportDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : exportDecl input = .reject failure rejected) :
    DeclarativeGrammar.ExportDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold exportDecl at result
  cases keywordResult : keyword .exportKw .exportDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have keywordRejectedEq := exportKeyword_reject_state_eq keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (exportKeyword_reject_tokenKindAbsentAt keywordResult)
  | ok keyword afterKeyword =>
      have keywordParsed := keyword_success_exactTokenParses .exportKw
        .exportDecl keywordResult
      simp only [bind, keywordResult, getState] at result
      by_cases leftBracePresent : isSymbol afterKeyword .leftBrace = true
      · simp only [leftBracePresent, if_true] at result
        exact .localRejected keyword.span keywordParsed
          (exportDeclLeftBracePresentAt_of_isSymbol_eq_true leftBracePresent)
          (localExport_reject_ordinaryOutcome_sound keyword.span result)
      · have leftBraceAbsent : isSymbol afterKeyword .leftBrace = false :=
          Bool.eq_false_iff.mpr leftBracePresent
        simp only [leftBraceAbsent, Bool.false_eq_true, if_false] at result
        exact .pathRejected keyword.span keywordParsed
          (symbolAbsentAt_of_isSymbol_eq_false .leftBrace leftBraceAbsent)
          (pathExport_reject_ordinaryOutcome_sound keyword.span result)

end Solcore.Syntax.Parser
