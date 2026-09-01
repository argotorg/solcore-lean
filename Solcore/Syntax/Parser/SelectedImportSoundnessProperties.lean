import Solcore.Syntax.Parser.PlainImportSoundnessProperties
import Solcore.Syntax.Parser.SelectorNameSoundnessProperties

/-! Success soundness of selected import names and aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional alias parsing is maximal and follows the exact token grammar. -/
theorem selectedAlias_success_sound {input next : State}
    {alias : Option Identifier}
    (result : ImportInternals.selectedAlias input = .ok alias next) :
    DeclarativeGrammar.SelectedAliasParses input.declarativeRemainder alias
      next.declarativeRemainder := by
  unfold ImportInternals.selectedAlias at result
  simp only [getState, bind] at result
  split at result
  next present =>
    rcases importBind_success_components result with
      ⟨asToken, afterAs, asResult, rest⟩
    rcases importBind_success_components rest with
      ⟨name, afterName, nameResult, finished⟩
    cases finished
    have asSound := keyword_ok_tokenAt .asKw .importDecl asResult
    have nameSound := identifier_ok_tokenAt .importDecl nameResult
    apply DeclarativeGrammar.SelectedAliasParses.present asToken.span asSound.1
      (by simpa only [asSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using nameSound.1)
    · simp only [State.declarativeRemainder, nameSound.2.1, asSound.2]
    · simp only [State.declarativeRemainder, nameSound.2.2.1, asSound.2]
    · simp only [State.declarativeRemainder, nameSound.2.2.2, asSound.2,
        Nat.add_assoc]
  next absent =>
    simp only [pure] at result
    cases result
    have absentFalse : isKeyword input .asKw = false := by
      cases found : isKeyword input .asKw <;> simp_all
    exact .absent (keywordAbsentAt_of_isKeyword_eq_false .asKw
      absentFalse)

/-- Alias grammar soundness composes with source-provenance validity. -/
theorem selectedAlias_success_sound_and_validFor {input next : State}
    {alias : Option Identifier} (inputValid : input.ValidFor)
    (result : ImportInternals.selectedAlias input = .ok alias next) :
    DeclarativeGrammar.SelectedAliasParses input.declarativeRemainder alias
        next.declarativeRemainder ∧
      Option.ValidFor Located.ValidFor input.file alias := by
  refine ⟨selectedAlias_success_sound result, ?_⟩
  have valid := selectedAlias_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Every selected import item follows the selector-and-alias grammar. -/
theorem selectedImport_success_sound {input next : State}
    {selection : SelectedImport}
    (result : selectedImport input = .ok selection next) :
    DeclarativeGrammar.SelectedImportParses input.declarativeRemainder
      selection next.declarativeRemainder := by
  unfold selectedImport at result
  rcases importBind_success_components result with
    ⟨source, afterSource, sourceResult, rest⟩
  rcases importBind_success_components rest with
    ⟨alias, afterAlias, aliasResult, finished⟩
  cases finished
  refine ⟨afterSource.declarativeRemainder,
    selectorName_success_sound .importDecl sourceResult,
    selectedAlias_success_sound aliasResult, ?_⟩
  cases alias <;> rfl

/-- Selected-import grammar soundness composes with source validity. -/
theorem selectedImport_success_sound_and_validFor {input next : State}
    {selection : SelectedImport} (inputValid : input.ValidFor)
    (result : selectedImport input = .ok selection next) :
    DeclarativeGrammar.SelectedImportParses input.declarativeRemainder
        selection next.declarativeRemainder ∧
      selection.ValidFor input.file := by
  refine ⟨selectedImport_success_sound result, ?_⟩
  have valid := selectedImport_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
