import Solcore.Syntax.DeclarativePragmaRejectionTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties
import Solcore.Syntax.Parser.PragmaDeclarationTraceProperties
import Solcore.Syntax.Parser.PragmaItemsContextProperties
import Solcore.Syntax.Parser.PragmaItemsRejectionTraceCompletenessProperties

/-! Exact uncommitted failures and retained events for complete pragma rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every rejected declaration realizes exactly one independent failing stage.
Only completed checked items have emitted events; the failure remains uncommitted. -/
theorem pragmaDecl_reject_trace_sound
    {input rejected : State} {failure : Failure}
    (result : pragmaDecl input = .reject failure rejected) :
    ∃ trace,
      DeclarativeGrammar.PragmaDeclTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder
        failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .pragmaKw .pragmaDecl keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      refine ⟨[], .keywordMissing
        (keyword_reject_tokenKindAbsentAt .pragmaKw .pragmaDecl keywordResult)
        (acceptToken_reject_reports (.keyword .pragmaKw) .pragmaDecl
          (· == .keyword .pragmaKw) keywordResult).1, ?_⟩
      simp only [List.append_nil]
  | ok pragmaKeyword afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordParsed := keyword_success_exactTokenParses .pragmaKw .pragmaDecl keywordResult
      have keywordShape := (keyword_ok_tokenAt .pragmaKw .pragmaDecl keywordResult).2
      have keywordSilent := acceptToken_success_diagnostics_eq
        (.keyword .pragmaKw) .pragmaDecl (· == .keyword .pragmaKw) keywordResult
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          have checked : identifier .pragmaDecl afterKeyword =
              .reject nameFailure nameRejected := by simp only [identifier, nameResult]
          have rejectedEq := identifier_reject_state_eq .pragmaDecl checked
          subst nameRejected
          simp only [nameResult] at result
          cases result
          refine ⟨[], .nameRejected pragmaKeyword.span keywordParsed
            (rawIdentifier_reject_ordinaryOutcome_sound .pragmaDecl nameResult) ?_, ?_⟩
          · have report := ((rawIdentifier_reject_reports_iff .pragmaDecl).mpr
              ⟨failure, nameResult, rfl⟩).2
            simpa only [keywordShape] using report
          · simpa only [List.append_nil] using keywordSilent
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := rawIdentifier_success_ordinaryOutcome_sound .pragmaDecl nameResult
          have nameShape := (rawIdentifier_ok_tokenAt .pragmaDecl nameResult).2
          have nameSilent := rawIdentifier_success_diagnostics_eq .pragmaDecl nameResult
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject itemsFailure itemsRejected =>
              simp only [itemsResult] at result
              cases result
              rcases PragmaInternals.pragmaItems_reject_trace_sound itemsResult with
                ⟨trace, traced, diagnostics⟩
              refine ⟨trace, .itemsRejected pragmaKeyword.span keywordParsed nameParsed ?_, ?_⟩
              · simpa only [nameShape, keywordShape] using traced
              · rw [diagnostics, nameSilent, keywordSilent]
          | ok items afterItems =>
              simp only [itemsResult] at result
              rcases PragmaInternals.pragmaItems_success_trace_sound itemsResult with
                ⟨trace, itemsParsed, diagnostics⟩
              have itemsContext := PragmaInternals.pragmaItems_success_context_eq itemsResult
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | ok semicolon output => simp [semicolonResult, pure] at result
              | reject semicolonFailure semicolonRejected =>
                  have rejectedEq := symbol_reject_state_eq .semicolon .pragmaDecl semicolonResult
                  subst semicolonRejected
                  simp only [semicolonResult] at result
                  cases result
                  refine ⟨trace, .semicolonMissing pragmaKeyword.span keywordParsed nameParsed
                    itemsParsed (symbol_reject_tokenKindAbsentAt .semicolon .pragmaDecl
                      semicolonResult) ?_, ?_⟩
                  · have report := (acceptToken_reject_reports (.symbol .semicolon) .pragmaDecl
                      (· == .symbol .semicolon) semicolonResult).1
                    simpa only [itemsContext.1, itemsContext.2, nameShape, keywordShape] using report
                  · rw [diagnostics, nameSilent, keywordSilent]

end Solcore.Syntax.Parser
