import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.PrimitiveCarrierProperties

/-! Compositional contracts for canonical import parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem importBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem getState_preservesTokenWindow :
    Parser.PreservesTokenWindow getState := by
  intro input
  exact ⟨rfl, rfl⟩

/-- Optional selected-import aliases retain their identifier range. -/
theorem selectedAlias_validFor :
    ImportInternals.selectedAlias.ValidFor
      (Option.ValidFor Located.ValidFor) := by
  unfold ImportInternals.selectedAlias
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .asKw
  · simp only [present, if_true]
    apply Parser.bind_validFor (keyword_validFor .asKw .importDecl)
    intro marker
    apply Parser.bind_validFor_of_value (identifier_validFor .importDecl)
    intro name input inputValid nameValid
    exact ⟨by simpa only [Option.ValidFor] using nameValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none
      (Option.ValidFor Located.ValidFor) (fun _ => trivial)

/-- Optional aliases preserve every ordinary token window. -/
theorem selectedAlias_preservesTokenWindow :
    Parser.PreservesTokenWindow ImportInternals.selectedAlias := by
  unfold ImportInternals.selectedAlias
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases present : isKeyword observed .asKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .asKw .importDecl)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (identifier_preservesTokenWindow .importDecl)
    intro name
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Optional aliases preserve the immutable token carrier on success. -/
theorem selectedAlias_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ImportInternals.selectedAlias :=
  selectedAlias_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional selected-import aliases never rewind the parser cursor. -/
theorem selectedAlias_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ImportInternals.selectedAlias := by
  unfold ImportInternals.selectedAlias
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .asKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .asKw .importDecl)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (identifier_cursorMonotoneOnSuccess .importDecl)
    intro name
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- Selected imports preserve every ordinary token window. -/
theorem selectedImport_preservesTokenWindow :
    Parser.PreservesTokenWindow selectedImport := by
  unfold selectedImport
  apply Parser.bind_preservesTokenWindow
    (selectorName_preservesTokenWindow .importDecl)
  intro source
  apply Parser.bind_preservesTokenWindow selectedAlias_preservesTokenWindow
  intro alias
  exact Parser.pure_preservesTokenWindow _

/-- Selected imports preserve the immutable token carrier on success. -/
theorem selectedImport_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess selectedImport :=
  selectedImport_preservesTokenWindow.preservesTokensOnSuccess

/-- Selected imports never rewind the parser cursor. -/
theorem selectedImport_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess selectedImport := by
  unfold selectedImport
  apply Parser.bind_cursorMonotoneOnSuccess
    (selectorName_cursorMonotoneOnSuccess .importDecl)
  intro source
  apply Parser.bind_cursorMonotoneOnSuccess
    selectedAlias_cursorMonotoneOnSuccess
  intro alias
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A selected import starts at its retained selector token. -/
theorem selectedImport_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess selectedImport (·.span) := by
  unfold selectedImport
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (selectorName_startsAtCurrentTokenOnSuccess .importDecl)
  intro source input selection final parsed
  rcases importBind_ok_components parsed with
    ⟨alias, afterAlias, _aliasResult, finished⟩
  cases alias <;> cases finished <;> rfl

end Solcore.Syntax.Parser
