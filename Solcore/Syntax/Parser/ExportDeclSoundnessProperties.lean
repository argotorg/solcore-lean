import Solcore.Syntax.Parser.LocalExportSoundnessProperties
import Solcore.Syntax.Parser.PathExportSoundnessProperties

/-! Aggregate success soundness of all canonical export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful export follows one exact declarative form. -/
theorem exportDecl_success_sound {input next : State}
    {declaration : ExportDecl}
    (result : exportDecl input = .ok declaration next) :
    DeclarativeGrammar.ExportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder := by
  unfold exportDecl at result
  cases keywordResult : keyword .exportKw .exportDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject failure rejected => simp [bind, keywordResult] at result
  | ok exportKeyword afterKeyword =>
      have keywordSound := keyword_ok_tokenAt .exportKw .exportDecl
        keywordResult
      simp only [bind, keywordResult, getState] at result
      split at result
      · have tailGrammar := localExport_success_sound exportKeyword.span
          result
        apply DeclarativeGrammar.ExportDeclParses.ofLocal
        unfold DeclarativeGrammar.LocalExportDeclParses
        refine ⟨exportKeyword.span, keywordSound.1, ?_⟩
        simpa only [keywordSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using tailGrammar
      · have leftBraceFalse :
            isSymbol afterKeyword .leftBrace = false := by
          cases found : isSymbol afterKeyword .leftBrace <;> simp_all
        have leftBraceAbsentAfter := symbolAbsentAt_of_isSymbol_eq_false
          .leftBrace leftBraceFalse
        have leftBraceAbsentInput :
            DeclarativeGrammar.TokenKindAbsentAt input.tokens
              input.window.endIndex (input.cursor + 1)
              (.symbol .leftBrace) := by
          simpa only [keywordSound.2, State.tokens, State.window,
            State.cursor] using leftBraceAbsentAfter
        have tailGrammar := pathExport_success_sound exportKeyword.span result
        cases tailGrammar with
        | itemsFrom parsed =>
            apply DeclarativeGrammar.ExportDeclParses.ofItemsFrom
            unfold DeclarativeGrammar.ItemsFromExportDeclParses
            refine ⟨exportKeyword.span, keywordSound.1,
              leftBraceAbsentInput, ?_⟩
            simpa only [keywordSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using parsed
        | moduleAs parsed =>
            apply DeclarativeGrammar.ExportDeclParses.ofModuleAs
            unfold DeclarativeGrammar.ModuleAsExportDeclParses
            refine ⟨exportKeyword.span, keywordSound.1,
              leftBraceAbsentInput, ?_⟩
            simpa only [keywordSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using parsed
        | module parsed =>
            apply DeclarativeGrammar.ExportDeclParses.ofModule
            unfold DeclarativeGrammar.ModuleExportDeclParses
            refine ⟨exportKeyword.span, keywordSound.1,
              leftBraceAbsentInput, ?_⟩
            simpa only [keywordSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using parsed

/-- Aggregate export grammar soundness composes with source validity. -/
theorem exportDecl_success_sound_and_validFor {input next : State}
    {declaration : ExportDecl} (inputValid : input.ValidFor)
    (result : exportDecl input = .ok declaration next) :
    DeclarativeGrammar.ExportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨exportDecl_success_sound result, ?_⟩
  have valid := exportDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
