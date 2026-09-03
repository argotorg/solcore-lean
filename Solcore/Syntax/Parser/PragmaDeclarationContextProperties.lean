import Solcore.Syntax.Parser.PragmaItemsContextProperties
import Solcore.Syntax.Parser.PragmaDeclarationOrdinaryOutcomeSoundnessProperties

/-! Unconditional file and complete-window frame laws for pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful declarations retain the source file and the full report window,
including its end byte, independently of emitted events and input validity. -/
theorem pragmaDecl_success_context_eq
    {input output : State} {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject failure rejected => simp [bind, keywordResult] at result
  | ok marker afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordShape := (keyword_ok_tokenAt .pragmaKw .pragmaDecl keywordResult).2
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          have nameShape := (rawIdentifier_ok_tokenAt .pragmaDecl nameResult).2
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject failure rejected => simp [itemsResult] at result
          | ok items afterItems =>
              simp only [itemsResult] at result
              have frame := PragmaInternals.pragmaItems_success_context_eq itemsResult
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | reject failure rejected => simp [semicolonResult] at result
              | ok semicolon afterSemicolon =>
                  simp only [semicolonResult] at result
                  cases result
                  have shape := (symbol_ok_tokenAt .semicolon .pragmaDecl semicolonResult).2
                  simp only [shape, frame.1, frame.2, nameShape, keywordShape, and_self]

/-- All rejecting stages retain the original source and complete window even
when earlier successful checked items have emitted diagnostics. -/
theorem pragmaDecl_reject_context_eq
    {input rejected : State} {failure : Failure}
    (result : pragmaDecl input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      simp only [bind, keywordResult] at result
      cases result
      rw [keyword_reject_state_eq .pragmaKw .pragmaDecl keywordResult]
      exact ⟨rfl, rfl⟩
  | ok marker afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordShape := (keyword_ok_tokenAt .pragmaKw .pragmaDecl keywordResult).2
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          have checked : identifier .pragmaDecl afterKeyword = .reject failure rejected := by
            simp only [identifier, nameResult]
          rw [identifier_reject_state_eq .pragmaDecl checked, keywordShape]
          exact ⟨rfl, rfl⟩
      | ok name afterName =>
          simp only [nameResult] at result
          have nameShape := (rawIdentifier_ok_tokenAt .pragmaDecl nameResult).2
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject itemsFailure itemsRejected =>
              simp only [itemsResult] at result
              cases result
              have frame := PragmaInternals.pragmaItems_reject_context_eq itemsResult
              simp only [frame.1, frame.2, nameShape, keywordShape, and_self]
          | ok items afterItems =>
              simp only [itemsResult] at result
              have frame := PragmaInternals.pragmaItems_success_context_eq itemsResult
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | ok semicolon output => simp [semicolonResult, pure] at result
              | reject semicolonFailure semicolonRejected =>
                  simp only [semicolonResult] at result
                  cases result
                  rw [symbol_reject_state_eq .semicolon .pragmaDecl semicolonResult]
                  simp only [frame.1, frame.2, nameShape, keywordShape, and_self]

end Solcore.Syntax.Parser
