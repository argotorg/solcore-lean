import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.CollectionValidity

/-! Contracts for modifiers shared by constructors and fallback entries. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractEntryInternals

private theorem entryBind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
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

private theorem getState_preservesTokenWindowForEntry :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

private theorem emitDiagnostic_preservesTokenWindowForEntry
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  intro input
  unfold emitDiagnostic modifyState Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

/-- An optional modifier retains a valid marker whenever it is present. -/
theorem optionalModifier_validFor (modifier : HardKeyword) :
    (optionalModifier modifier).ValidFor
      (Option.ValidFor (fun file span => span.ValidFor file)) := by
  unfold optionalModifier
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed modifier
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (keyword_validFor modifier .contractMember)
    intro marker input inputValid markerValid
    exact ⟨by simpa only [Option.ValidFor, Located.ValidFor] using markerValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional modifier parsing preserves every ordinary token window. -/
theorem optionalModifier_preservesTokenWindow (modifier : HardKeyword) :
    Parser.PreservesTokenWindow (optionalModifier modifier) := by
  unfold optionalModifier
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindowForEntry
  intro observed
  by_cases present : isKeyword observed modifier
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow modifier .contractMember)
    intro marker
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem optionalModifier_preservesTokensOnSuccess (modifier : HardKeyword) :
    Parser.PreservesTokensOnSuccess (optionalModifier modifier) :=
  (optionalModifier_preservesTokenWindow modifier).preservesTokensOnSuccess

/-- Optional modifier parsing never rewinds the parser cursor. -/
theorem optionalModifier_cursorMonotoneOnSuccess (modifier : HardKeyword) :
    Parser.CursorMonotoneOnSuccess (optionalModifier modifier) := by
  unfold optionalModifier
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed modifier
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess modifier .contractMember)
    intro marker
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present optional modifier starts at the current keyword token. -/
theorem optionalModifier_some_startsAtCurrentTokenOnSuccess
    (modifier : HardKeyword) {input final : State} {span : SourceSpan}
    (parsed : optionalModifier modifier input = .ok (some span) final) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = span.startByte := by
  unfold optionalModifier getState at parsed
  simp only [bind] at parsed
  by_cases present : isKeyword input modifier
  · simp only [present, if_true] at parsed
    rcases entryBind_ok_components parsed with
      ⟨marker, afterMarker, markerResult, finished⟩
    have starts := acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword modifier) .contractMember (· == .keyword modifier)
      input marker afterMarker markerResult
    cases finished
    exact starts
  · simp only [present] at parsed
    change Reply.ok none input = .ok (some span) final at parsed
    cases parsed

/-- Implicit-public handling retains only a valid optional payable marker. -/
theorem implicitPublicModifiers_validFor (declaration : HardKeyword) :
    (implicitPublicModifiers declaration).ValidFor
      (Option.ValidFor (fun file span => span.ValidFor file)) := by
  unfold implicitPublicModifiers
  apply Parser.bind_validFor_of_value (optionalModifier_validFor .publicKw)
  intro publicMarker input inputValid publicValid
  cases publicMarker with
  | none =>
      change (optionalModifier .payableKw input).ValidFor input _
      exact optionalModifier_validFor .payableKw input inputValid
  | some span =>
      simp only [Option.ValidFor] at publicValid
      let diagnostic : ParseDiagnostic := {
        span
        kind := .constraintViolation (.implicitPublicModifier declaration)
      }
      change (optionalModifier .payableKw (input.emit diagnostic)).ValidFor
        input _
      have emittedValid := inputValid.emit_validFor diagnostic publicValid
      exact (optionalModifier_validFor .payableKw
        (input.emit diagnostic) emittedValid).of_file_eq (by
          simp [State.emit])

/-- Implicit-public handling preserves every ordinary token window. -/
theorem implicitPublicModifiers_preservesTokenWindow
    (declaration : HardKeyword) :
    Parser.PreservesTokenWindow (implicitPublicModifiers declaration) := by
  unfold implicitPublicModifiers
  apply Parser.bind_preservesTokenWindow
    (optionalModifier_preservesTokenWindow .publicKw)
  intro publicMarker
  cases publicMarker with
  | none =>
      simp only
      exact optionalModifier_preservesTokenWindow .payableKw
  | some span =>
      simp only
      apply Parser.bind_preservesTokenWindow
        (emitDiagnostic_preservesTokenWindowForEntry _)
      intro _
      exact optionalModifier_preservesTokenWindow .payableKw

theorem implicitPublicModifiers_preservesTokensOnSuccess
    (declaration : HardKeyword) :
    Parser.PreservesTokensOnSuccess (implicitPublicModifiers declaration) :=
  Parser.PreservesTokenWindow.preservesTokensOnSuccess
    (implicitPublicModifiers_preservesTokenWindow declaration)

/-- Implicit-public handling never rewinds the parser cursor. -/
theorem implicitPublicModifiers_cursorMonotoneOnSuccess
    (declaration : HardKeyword) :
    Parser.CursorMonotoneOnSuccess (implicitPublicModifiers declaration) := by
  unfold implicitPublicModifiers
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalModifier_cursorMonotoneOnSuccess .publicKw)
  intro publicMarker
  cases publicMarker with
  | none =>
      simp only
      exact optionalModifier_cursorMonotoneOnSuccess .payableKw
  | some span =>
      simp only
      apply Parser.bind_cursorMonotoneOnSuccess
        (emitDiagnostic_cursorMonotoneOnSuccess _)
      intro _
      exact optionalModifier_cursorMonotoneOnSuccess .payableKw

end ContractEntryInternals
end Solcore.Syntax.Parser
