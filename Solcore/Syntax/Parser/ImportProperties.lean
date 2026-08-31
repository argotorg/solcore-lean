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

private theorem selectedAlias_some_components {input next : State}
    {name : Identifier}
    (parsed : ImportInternals.selectedAlias input = .ok (some name) next) :
    ∃ marker afterMarker,
      keyword .asKw .importDecl input = .ok marker afterMarker ∧
        identifier .importDecl afterMarker = .ok name next := by
  unfold ImportInternals.selectedAlias at parsed
  rcases importBind_ok_components parsed with
    ⟨observed, afterObserved, observedResult, rest⟩
  unfold getState at observedResult
  cases observedResult
  split at rest
  · rcases importBind_ok_components rest with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases importBind_ok_components rest with
      ⟨parsedName, afterName, nameResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, markerResult, nameResult⟩
  · cases rest

/-- Selected imports retain their selector, alias, and covering range. -/
theorem selectedImport_validFor :
    selectedImport.ValidFor SelectedImport.ValidFor := by
  have weak : selectedImport.ValidFor (fun _ _ => True) := by
    unfold selectedImport
    apply Parser.bind_validFor (selectorName_validFor .importDecl)
    intro source
    apply Parser.bind_validFor selectedAlias_validFor
    intro alias
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : selectedImport input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok selection final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold selectedImport at stages
      rcases importBind_ok_components stages with
        ⟨source, afterSource, sourceResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨alias, afterAlias, aliasResult, finished⟩
      have sourceValid := selectorName_validFor .importDecl input inputValid
      rw [sourceResult] at sourceValid
      have aliasValid := selectedAlias_validFor afterSource sourceValid.2.1
      rw [aliasResult] at aliasValid
      cases alias with
      | none =>
          cases finished
          exact ⟨⟨sourceValid.1.1, sourceValid.1, by simp⟩,
            weakResult.2.1, weakResult.2.2⟩
      | some name =>
          rcases selectedAlias_some_components aliasResult with
            ⟨marker, afterMarker, markerResult, nameResult⟩
          rcases selectorName_startsAtCurrentTokenOnSuccess .importDecl
              input source afterSource sourceResult with
            ⟨firstToken, firstFound, sourceStart⟩
          rcases identifier_ok_state_shape .importDecl nameResult with
            ⟨nameToken, nameFound, nameSpan, _nameTokens, _nameCursor⟩
          have firstAt :=
            State.getElem?_eq_some_of_peek?_eq_some firstFound
          have nameAt : input.tokens[afterMarker.cursor]? = some nameToken := by
            have foundAt :=
              State.getElem?_eq_some_of_peek?_eq_some nameFound
            have sourceTokens := selectorName_preservesTokensOnSuccess
              .importDecl input source afterSource sourceResult
            have markerTokens := keyword_preservesTokensOnSuccess .asKw
              .importDecl afterSource marker afterMarker markerResult
            simpa [markerTokens, sourceTokens] using foundAt
          have firstBeforeName :
              firstToken.span.endByte ≤ nameToken.span.startByte := by
            apply inputValid.token_end_le_token_start_of_getElem?_lt
              firstAt nameAt
            have sourceProgress :=
              selectorName_cursor_lt_onSuccess .importDecl sourceResult
            have markerShape := acceptToken_ok_state_shape
              (.keyword .asKw) .importDecl (· == .keyword .asKw) markerResult
            exact Nat.lt_trans sourceProgress (by simp [markerShape.2])
          have sourceSpanValid : source.span.ValidFor input.file :=
            sourceValid.1.1
          have nameSpanValid : name.span.ValidFor input.file := by
            have retained : Located.ValidFor afterSource.file name := by
              simpa only [Option.ValidFor] using aliasValid.1
            simpa [Located.ValidFor, sourceValid.2.2] using retained
          have firstSpanValid := inputValid.peek?_span_validFor firstFound
          have ordered : source.span.startByte ≤ name.span.endByte := by
            calc
              source.span.startByte = firstToken.span.startByte :=
                sourceStart.symm
              _ ≤ firstToken.span.endByte := firstSpanValid.2.1
              _ ≤ nameToken.span.startByte := firstBeforeName
              _ ≤ name.span.endByte := by
                rw [nameSpan]
                exact nameSpanValid.2.1
          have coverValid := SourceSpan.cover_validFor sourceSpanValid
            nameSpanValid ordered
          cases finished
          exact ⟨⟨coverValid, sourceValid.1, by simpa using nameSpanValid⟩,
            weakResult.2.1, weakResult.2.2⟩

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
