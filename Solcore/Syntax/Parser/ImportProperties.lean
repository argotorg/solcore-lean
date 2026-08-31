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

private theorem requireSelectorNames_validFor
    (values : DelimitedList SelectorName) :
    (ImportInternals.requireSelectorNames values).ValidFor
      (fun _ _ => True) := by
  intro input inputValid
  unfold ImportInternals.requireSelectorNames
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨trivial, inputValid, rfl⟩

private theorem requireSelectorNames_preservesTokenWindow
    (values : DelimitedList SelectorName) :
    Parser.PreservesTokenWindow
      (ImportInternals.requireSelectorNames values) := by
  intro input
  unfold ImportInternals.requireSelectorNames
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨rfl, rfl⟩

private theorem requireSelectorNames_cursorMonotoneOnSuccess
    (values : DelimitedList SelectorName) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.requireSelectorNames values) := by
  intro input names next result
  unfold ImportInternals.requireSelectorNames at result
  cases elements : values.elements with
  | nil =>
      rw [elements] at result
      contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact Nat.le_refl _

/-- Hiding clauses retain their keyword cover and every selector range. -/
theorem hidingClause_validFor :
    ImportInternals.hidingClause.ValidFor HidingClause.ValidFor := by
  have weak : ImportInternals.hidingClause.ValidFor
      (fun _ _ => True) := by
    unfold ImportInternals.hidingClause
    apply Parser.bind_validFor
      (contextual_validFor .hiding .importDecl)
    intro marker
    apply Parser.bind_validFor (delimited_validFor SelectorName.ValidFor
      .leftBrace .rightBrace false (selectorName .importDecl)
      .importDecl .topLevel (selectorName_validFor .importDecl)
      (selectorName_preservesTokensOnSuccess .importDecl))
    intro values
    apply Parser.bind_validFor (requireSelectorNames_validFor values)
    intro names
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : ImportInternals.hidingClause input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok clause final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold ImportInternals.hidingClause at stages
      rcases importBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨values, afterValues, valuesResult, rest⟩
      rcases importBind_ok_components rest with
        ⟨names, afterNames, namesResult, finished⟩
      have markerValid := contextual_validFor .hiding .importDecl
        input inputValid
      rw [markerResult] at markerValid
      have valuesValid := delimited_validFor SelectorName.ValidFor
        .leftBrace .rightBrace false (selectorName .importDecl)
        .importDecl .topLevel (selectorName_validFor .importDecl)
        (selectorName_preservesTokensOnSuccess .importDecl)
        afterMarker markerValid.2.1
      rw [valuesResult] at valuesValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have valuesValidInput :
          DelimitedList.ValidFor SelectorName.ValidFor input.file values := by
        simpa [markerValid.2.2] using valuesValid.1
      have markerShape := acceptToken_ok_state_shape
        (.contextual .hiding) .importDecl (·.isContextual .hiding)
        markerResult
      have markerAdvanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      rcases delimited_startsAtCurrentTokenOnSuccess .leftBrace .rightBrace
          false (selectorName .importDecl) .importDecl .topLevel
          afterMarker values afterValues valuesResult with
        ⟨opening, openingFound, valuesStart⟩
      have markerBeforeValues :=
        inputValid.consumed_end_le_peek_start_after_advance
          markerAdvanced openingFound
      have ordered : marker.span.startByte ≤ values.span.endByte :=
        Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeValues (by
            rw [valuesStart]
            exact valuesValidInput.1.2.1))
      unfold ImportInternals.requireSelectorNames at namesResult
      cases elements : values.elements with
      | nil =>
          rw [elements] at namesResult
          contradiction
      | cons head tail =>
          rw [elements] at namesResult
          cases namesResult
          cases finished
          exact ⟨⟨SourceSpan.cover_validFor markerSpanValid
              valuesValidInput.1 ordered, by
                simpa [NonemptyList.toList, elements] using
                  valuesValidInput.2⟩,
            weakResult.2.1, weakResult.2.2⟩

/-- Hiding clauses preserve every ordinary token window. -/
theorem hidingClause_preservesTokenWindow :
    Parser.PreservesTokenWindow ImportInternals.hidingClause := by
  unfold ImportInternals.hidingClause
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .hiding .importDecl)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel
      (selectorName_preservesTokenWindow .importDecl))
  intro values
  apply Parser.bind_preservesTokenWindow
    (requireSelectorNames_preservesTokenWindow values)
  intro names
  exact Parser.pure_preservesTokenWindow _

theorem hidingClause_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ImportInternals.hidingClause :=
  hidingClause_preservesTokenWindow.preservesTokensOnSuccess

/-- Hiding clauses never rewind the parser cursor. -/
theorem hidingClause_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ImportInternals.hidingClause := by
  unfold ImportInternals.hidingClause
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .hiding .importDecl)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftBrace .rightBrace false
      (selectorName .importDecl) .importDecl .topLevel)
  intro values
  apply Parser.bind_cursorMonotoneOnSuccess
    (requireSelectorNames_cursorMonotoneOnSuccess values)
  intro names
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A hiding clause starts at its `hiding` token. -/
theorem hidingClause_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ImportInternals.hidingClause (·.span) := by
  unfold ImportInternals.hidingClause
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.contextual .hiding) .importDecl (·.isContextual .hiding))
  intro marker input clause final parsed
  rcases importBind_ok_components parsed with
    ⟨values, afterValues, _valuesResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨names, afterNames, _namesResult, finished⟩
  cases finished
  rfl

/-- Optional hiding clauses preserve present-clause provenance. -/
theorem optionalHiding_validFor :
    ImportInternals.optionalHiding.ValidFor
      (Option.ValidFor HidingClause.ValidFor) := by
  unfold ImportInternals.optionalHiding
  apply Parser.bind_validFor getState_validFor
  intro observed
  split
  · apply Parser.bind_validFor_of_value hidingClause_validFor
    intro clause input inputValid clauseValid
    exact ⟨by simpa only [Option.ValidFor] using clauseValid,
      inputValid, rfl⟩
  · exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional hiding clauses preserve every ordinary token window. -/
theorem optionalHiding_preservesTokenWindow :
    Parser.PreservesTokenWindow ImportInternals.optionalHiding := by
  unfold ImportInternals.optionalHiding
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  split
  · apply Parser.bind_preservesTokenWindow hidingClause_preservesTokenWindow
    intro clause
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow none

theorem optionalHiding_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ImportInternals.optionalHiding :=
  optionalHiding_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional hiding clauses never rewind the parser cursor. -/
theorem optionalHiding_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ImportInternals.optionalHiding := by
  unfold ImportInternals.optionalHiding
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      hidingClause_cursorMonotoneOnSuccess
    intro clause
    exact Parser.pure_cursorMonotoneOnSuccess _
  · exact Parser.pure_cursorMonotoneOnSuccess none

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

private theorem requireSelected_validFor
    (values : DelimitedList SelectedImport) :
    (ImportInternals.requireSelected values).ValidFor
      (fun _ _ => True) := by
  intro input inputValid
  unfold ImportInternals.requireSelected
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨trivial, inputValid, rfl⟩

private theorem requireSelected_preservesTokenWindow
    (values : DelimitedList SelectedImport) :
    Parser.PreservesTokenWindow
      (ImportInternals.requireSelected values) := by
  intro input
  unfold ImportInternals.requireSelected
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨rfl, rfl⟩

private theorem requireSelected_cursorMonotoneOnSuccess
    (values : DelimitedList SelectedImport) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.requireSelected values) := by
  intro input selection next result
  unfold ImportInternals.requireSelected at result
  cases elements : values.elements with
  | nil =>
      rw [elements] at result
      contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact Nat.le_refl _

/-- A nonempty selected-import list retains delimiters and every item. -/
theorem selectedImports_validFor :
    ImportInternals.selectedImports.ValidFor
      (NonemptyDelimitedList.ValidFor SelectedImport.ValidFor) := by
  have weak : ImportInternals.selectedImports.ValidFor
      (fun _ _ => True) := by
    unfold ImportInternals.selectedImports
    apply Parser.bind_validFor (delimited_validFor SelectedImport.ValidFor
      .leftBrace .rightBrace false selectedImport .importDecl .topLevel
      selectedImport_validFor selectedImport_preservesTokensOnSuccess)
    intro values
    exact requireSelected_validFor values
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : ImportInternals.selectedImports input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok selection final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold ImportInternals.selectedImports at stages
      rcases importBind_ok_components stages with
        ⟨values, afterValues, valuesResult, selectionResult⟩
      have valuesValid := delimited_validFor SelectedImport.ValidFor
        .leftBrace .rightBrace false selectedImport .importDecl .topLevel
        selectedImport_validFor selectedImport_preservesTokensOnSuccess
        input inputValid
      rw [valuesResult] at valuesValid
      unfold ImportInternals.requireSelected at selectionResult
      cases elements : values.elements with
      | nil =>
          rw [elements] at selectionResult
          contradiction
      | cons head tail =>
          rw [elements] at selectionResult
          cases selectionResult
          exact ⟨⟨valuesValid.1.1, by
              intro item member
              exact valuesValid.1.2 item (by
                simpa [NonemptyList.toList, elements] using member)⟩,
            weakResult.2.1, weakResult.2.2⟩

/-- Selected-import lists preserve every ordinary token window. -/
theorem selectedImports_preservesTokenWindow :
    Parser.PreservesTokenWindow ImportInternals.selectedImports := by
  unfold ImportInternals.selectedImports
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftBrace .rightBrace false
      selectedImport .importDecl .topLevel
      selectedImport_preservesTokenWindow)
  intro values
  exact requireSelected_preservesTokenWindow values

theorem selectedImports_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ImportInternals.selectedImports :=
  selectedImports_preservesTokenWindow.preservesTokensOnSuccess

/-- Selected-import lists never rewind the parser cursor. -/
theorem selectedImports_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ImportInternals.selectedImports := by
  unfold ImportInternals.selectedImports
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftBrace .rightBrace false
      selectedImport .importDecl .topLevel)
  intro values
  exact requireSelected_cursorMonotoneOnSuccess values

/-- A selected-import list starts at its opening brace. -/
theorem selectedImports_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ImportInternals.selectedImports (·.span) := by
  unfold ImportInternals.selectedImports
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimited_startsAtCurrentTokenOnSuccess .leftBrace .rightBrace false
      selectedImport .importDecl .topLevel)
  intro values input selection final parsed
  unfold ImportInternals.requireSelected at parsed
  cases elements : values.elements with
  | nil =>
      rw [elements] at parsed
      contradiction
  | cons head tail =>
      rw [elements] at parsed
      cases parsed
      rfl

end Solcore.Syntax.Parser
