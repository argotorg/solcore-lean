import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.ExportNameSoundnessProperties

/-! Success soundness of canonical remote export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful remote selection follows its prioritized grammar. -/
theorem exportSelection_success_sound {input next : State}
    {selection : ExportSelection}
    (result : ExportInternals.exportSelection input = .ok selection next) :
    DeclarativeGrammar.ExportSelectionParses input.declarativeRemainder
      selection next.declarativeRemainder := by
  unfold ExportInternals.exportSelection at result
  split at result
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        have markerSound := symbol_ok_tokenAt .star .exportDecl markerResult
        simp only [markerResult] at result
        cases result
        have grammar := DeclarativeGrammar.ExportSelectionParses.wildcard
          (input := input.declarativeRemainder) marker.span markerSound.1
        simpa only [markerSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using grammar
  · have starFalse : isSymbol input .star = false := by
      cases found : isSymbol input .star <;> simp_all
    have starAbsent := symbolAbsentAt_of_isSymbol_eq_false .star starFalse
    cases itemsResult : delimited .leftBrace .rightBrace true
        ExportInternals.exportName .exportDecl .topLevel input with
    | invariant error => simp [itemsResult] at result
    | reject failure rejected => simp [itemsResult] at result
    | ok items afterItems =>
        have itemsGrammar := delimited_allowEmpty_trailing_success_sound
          .leftBrace .rightBrace ExportInternals.exportName
          DeclarativeGrammar.ExportNameParses .exportDecl .topLevel
          exportName_success_sound exportName_preservesTokenWindow itemsResult
        simp only [itemsResult] at result
        cases result
        exact DeclarativeGrammar.ExportSelectionParses.selected starAbsent
          itemsGrammar

/-- Remote-selection grammar soundness composes with source validity. -/
theorem exportSelection_success_sound_and_validFor {input next : State}
    {selection : ExportSelection} (inputValid : input.ValidFor)
    (result : ExportInternals.exportSelection input = .ok selection next) :
    DeclarativeGrammar.ExportSelectionParses input.declarativeRemainder
        selection next.declarativeRemainder ∧
      selection.ValidFor input.file := by
  refine ⟨exportSelection_success_sound result, ?_⟩
  have valid := exportSelection_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
