import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.ImportProperties
import Solcore.Syntax.Parser.SelectedImportSoundnessProperties

/-! Success soundness of nonempty selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- `requireSelected` preserves state, delimiter span, and forward elements. -/
theorem requireSelected_success_shape
    {values : DelimitedList SelectedImport}
    {input next : State}
    {selection : NonemptyDelimitedList SelectedImport}
    (result : ImportInternals.requireSelected values input =
      .ok selection next) :
    next = input ∧
      selection.span = values.span ∧
      selection.elements.toList = values.elements := by
  unfold ImportInternals.requireSelected at result
  cases elements : values.elements with
  | nil =>
      rw [elements] at result
      contradiction
  | cons head tail =>
      rw [elements] at result
      simp only [pure] at result
      cases result
      exact ⟨rfl, rfl, by simp [NonemptyList.toList]⟩

/-- Every successful selected-import list follows the independent grammar. -/
theorem selectedImports_success_sound {input next : State}
    {selection : NonemptyDelimitedList SelectedImport}
    (result : ImportInternals.selectedImports input = .ok selection next) :
    DeclarativeGrammar.SelectedImportsParses input.declarativeRemainder
      selection next.declarativeRemainder := by
  unfold ImportInternals.selectedImports at result
  cases valuesResult : delimited .leftBrace .rightBrace false selectedImport
      .importDecl .topLevel input with
  | invariant error => simp [bind, valuesResult] at result
  | reject failure rejected => simp [bind, valuesResult] at result
  | ok values afterValues =>
      simp only [bind, valuesResult] at result
      have valuesGrammar := delimited_nonempty_trailing_success_sound
        .leftBrace .rightBrace selectedImport
        DeclarativeGrammar.SelectedImportParses .importDecl .topLevel
        selectedImport_success_sound selectedImport_preservesTokenWindow
        valuesResult
      have shape := requireSelected_success_shape result
      unfold DeclarativeGrammar.SelectedImportsParses
      rw [shape.1]
      simpa only [shape.2.1, shape.2.2] using valuesGrammar

/-- Selected-list grammar soundness composes with source validity. -/
theorem selectedImports_success_sound_and_validFor {input next : State}
    {selection : NonemptyDelimitedList SelectedImport}
    (inputValid : input.ValidFor)
    (result : ImportInternals.selectedImports input = .ok selection next) :
    DeclarativeGrammar.SelectedImportsParses input.declarativeRemainder
        selection next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor SelectedImport.ValidFor input.file
        selection := by
  refine ⟨selectedImports_success_sound result, ?_⟩
  have valid := selectedImports_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
