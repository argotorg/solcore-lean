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

/-- Import terminators retain a semicolon or the validated recovery span. -/
theorem importTerminator_validFor (lastSpan : SourceSpan)
    (input : State) (inputValid : input.ValidFor)
    (lastValid : lastSpan.ValidFor input.file) :
    (ImportInternals.terminator lastSpan input).ValidFor input
      (fun file span => span.ValidFor file) := by
  unfold ImportInternals.terminator
  split
  · cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have valid := symbol_validFor .semicolon .importDecl input inputValid
        rw [semicolonResult] at valid
        simpa only [Reply.ValidFor] using valid
    | ok token next =>
        have valid := symbol_validFor .semicolon .importDecl input inputValid
        rw [semicolonResult] at valid
        exact ⟨by simpa only [Located.ValidFor] using valid.1,
          valid.2.1, valid.2.2⟩
  · split
    · exact ⟨lastValid,
        inputValid.emit_validFor _ inputValid.currentSpan_validFor, rfl⟩
    · unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩

private theorem importTerminator_end_order (start last : SourceSpan)
    (input : State) (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    (ordered : start.startByte ≤ last.endByte)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor)
    {endSpan : SourceSpan} {next : State}
    (parsed : ImportInternals.terminator last input = .ok endSpan next) :
    start.startByte ≤ endSpan.endByte := by
  unfold ImportInternals.terminator at parsed
  by_cases present : isSymbol input .semicolon
  · simp only [present, if_true] at parsed
    cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at parsed
    | reject failure rejected => simp [semicolonResult] at parsed
    | ok semicolon afterSemicolon =>
        simp only [semicolonResult] at parsed
        cases parsed
        have semicolonShape :=
          symbol_ok_state_shape .semicolon .importDecl semicolonResult
        have semicolonAt :=
          State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
        have startBeforeSemicolon :=
          inputValid.token_end_le_token_start_of_getElem?_lt
            startFound semicolonAt startBefore
        have semicolonValid :=
          inputValid.peek?_span_validFor semicolonShape.1
        exact Nat.le_trans startValid.2.1
          (Nat.le_trans (by simpa [startSpan] using startBeforeSemicolon)
            semicolonValid.2.1)
  · simp only [present] at parsed
    by_cases topStart : atTopItemStart input = true
    · simp only [topStart, if_true] at parsed
      cases parsed
      exact ordered
    · simp only [topStart] at parsed
      unfold rejectAt at parsed
      contradiction

/-- Finishing an import preserves both its cover and payload provenance. -/
theorem finishImport_validFor (start last : SourceSpan)
    (value : ImportDeclValue) (input : State)
    (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    (lastValid : last.ValidFor input.file)
    (ordered : start.startByte ≤ last.endByte)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor)
    (valueValid : match value with
      | .plain modulePath => ModulePath.ValidFor input.file modulePath
      | .namespace modulePath alias =>
          ModulePath.ValidFor input.file modulePath ∧
            alias.span.ValidFor input.file
      | .wildcard modulePath hidingClause =>
          ModulePath.ValidFor input.file modulePath ∧
            ∀ clause ∈ hidingClause, HidingClause.ValidFor input.file clause
      | .selected selection modulePath hidingClause =>
          selection.span.ValidFor input.file ∧
            (∀ item ∈ selection.elements.toList,
              SelectedImport.ValidFor input.file item) ∧
            ModulePath.ValidFor input.file modulePath ∧
            ∀ clause ∈ hidingClause,
              HidingClause.ValidFor input.file clause) :
    (ImportInternals.finish start last value input).ValidFor input
      ImportDecl.ValidFor := by
  have terminatorValid := importTerminator_validFor last input inputValid lastValid
  unfold ImportInternals.finish
  cases terminatorResult : ImportInternals.terminator last input with
  | invariant error =>
      simp only [bind, terminatorResult, Reply.ValidFor]
  | reject failure rejected =>
      rw [terminatorResult] at terminatorValid
      simpa only [bind, terminatorResult, Reply.ValidFor] using
        terminatorValid
  | ok endSpan next =>
      rw [terminatorResult] at terminatorValid
      simp only [bind, terminatorResult, Reply.ValidFor, ImportDecl.ValidFor]
      refine ⟨⟨SourceSpan.cover_validFor startValid terminatorValid.1 ?_,
        valueValid⟩, terminatorValid.2.1, terminatorValid.2.2⟩
      exact importTerminator_end_order start last input inputValid startValid
        ordered startFound startSpan startBefore terminatorResult

/-- Import terminators preserve every ordinary token window. -/
theorem importTerminator_preservesTokenWindow (lastSpan : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.terminator lastSpan) := by
  intro input
  unfold ImportInternals.terminator
  split
  · have shape := symbol_preservesTokenWindow .semicolon .importDecl input
    cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [semicolonResult] at shape
        exact shape
    | ok token next =>
        rw [semicolonResult] at shape
        exact shape
  · split
    · exact ⟨rfl, rfl⟩
    · exact rejectAt_preservesTokenWindow input _ _

theorem importTerminator_preservesTokensOnSuccess (lastSpan : SourceSpan) :
    Parser.PreservesTokensOnSuccess
      (ImportInternals.terminator lastSpan) :=
  (importTerminator_preservesTokenWindow lastSpan).preservesTokensOnSuccess

/-- Import terminators either consume `;` or leave the cursor in place. -/
theorem importTerminator_cursorMonotoneOnSuccess (lastSpan : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.terminator lastSpan) := by
  intro input endSpan next parsed
  unfold ImportInternals.terminator at parsed
  split at parsed
  · cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at parsed
    | reject failure rejected => simp [semicolonResult] at parsed
    | ok token afterToken =>
        simp only [semicolonResult] at parsed
        cases parsed
        exact symbol_cursorMonotoneOnSuccess .semicolon .importDecl
          input token next semicolonResult
  · split at parsed
    · cases parsed
      exact Nat.le_refl _
    · unfold rejectAt at parsed
      contradiction

/-- Finishing an import preserves every ordinary token window. -/
theorem finishImport_preservesTokenWindow (start last : SourceSpan)
    (value : ImportDeclValue) :
    Parser.PreservesTokenWindow
      (ImportInternals.finish start last value) := by
  unfold ImportInternals.finish
  apply Parser.bind_preservesTokenWindow
    (importTerminator_preservesTokenWindow last)
  intro endSpan
  exact Parser.pure_preservesTokenWindow _

theorem finishImport_preservesTokensOnSuccess (start last : SourceSpan)
    (value : ImportDeclValue) :
    Parser.PreservesTokensOnSuccess
      (ImportInternals.finish start last value) :=
  (finishImport_preservesTokenWindow start last value).preservesTokensOnSuccess

/-- Finishing an import never rewinds the parser cursor. -/
theorem finishImport_cursorMonotoneOnSuccess (start last : SourceSpan)
    (value : ImportDeclValue) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.finish start last value) := by
  unfold ImportInternals.finish
  apply Parser.bind_cursorMonotoneOnSuccess
    (importTerminator_cursorMonotoneOnSuccess last)
  intro endSpan
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem finishImport_keepsStartByte (start last : SourceSpan)
    (value : ImportDeclValue) {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.finish start last value input =
      .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.finish at parsed
  rcases importBind_ok_components parsed with
    ⟨endSpan, afterEnd, _endResult, finished⟩
  cases finished
  rfl

theorem plainImport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.plainImport start) := by
  unfold ImportInternals.plainImport
  apply Parser.bind_preservesTokenWindow
    (modulePath_preservesTokenWindow .importDecl)
  intro path
  exact finishImport_preservesTokenWindow start path.span (.plain path)

theorem plainImport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.plainImport start) := by
  unfold ImportInternals.plainImport
  apply Parser.bind_cursorMonotoneOnSuccess
    (modulePath_cursorMonotoneOnSuccess .importDecl)
  intro path
  exact finishImport_cursorMonotoneOnSuccess start path.span (.plain path)

theorem namespaceImport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.namespaceImport start) := by
  unfold ImportInternals.namespaceImport
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .star .importDecl)
  intro star
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .asKw .importDecl)
  intro asMarker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .importDecl)
  intro alias
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .from .importDecl)
  intro fromMarker
  apply Parser.bind_preservesTokenWindow
    (modulePath_preservesTokenWindow .importDecl)
  intro path
  exact finishImport_preservesTokenWindow start path.span
    (.namespace path alias)

theorem namespaceImport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.namespaceImport start) := by
  unfold ImportInternals.namespaceImport
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .star .importDecl)
  intro star
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .asKw .importDecl)
  intro asMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .importDecl)
  intro alias
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (modulePath_cursorMonotoneOnSuccess .importDecl)
  intro path
  exact finishImport_cursorMonotoneOnSuccess start path.span
    (.namespace path alias)

theorem wildcardImport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.wildcardImport start) := by
  unfold ImportInternals.wildcardImport
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .star .importDecl)
  intro star
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .from .importDecl)
  intro fromMarker
  apply Parser.bind_preservesTokenWindow
    (modulePath_preservesTokenWindow .importDecl)
  intro path
  apply Parser.bind_preservesTokenWindow optionalHiding_preservesTokenWindow
  intro hidden
  exact finishImport_preservesTokenWindow start
    (match hidden with | some clause => clause.span | none => path.span)
    (.wildcard path hidden)

theorem wildcardImport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.wildcardImport start) := by
  unfold ImportInternals.wildcardImport
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .star .importDecl)
  intro star
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (modulePath_cursorMonotoneOnSuccess .importDecl)
  intro path
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalHiding_cursorMonotoneOnSuccess
  intro hidden
  exact finishImport_cursorMonotoneOnSuccess start
    (match hidden with | some clause => clause.span | none => path.span)
    (.wildcard path hidden)

theorem plainImport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.plainImport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.plainImport at parsed
  rcases importBind_ok_components parsed with
    ⟨path, afterPath, _pathResult, finished⟩
  exact finishImport_keepsStartByte start path.span (.plain path) finished

theorem namespaceImport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.namespaceImport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.namespaceImport at parsed
  rcases importBind_ok_components parsed with
    ⟨star, afterStar, _starResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨asMarker, afterAs, _asResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨alias, afterAlias, _aliasResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨fromMarker, afterFrom, _fromResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨path, afterPath, _pathResult, finished⟩
  exact finishImport_keepsStartByte start path.span
    (.namespace path alias) finished

theorem wildcardImport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.wildcardImport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.wildcardImport at parsed
  rcases importBind_ok_components parsed with
    ⟨star, afterStar, _starResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨fromMarker, afterFrom, _fromResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨path, afterPath, _pathResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨hidden, afterHidden, _hiddenResult, finished⟩
  cases hidden with
  | none =>
      exact finishImport_keepsStartByte start path.span
        (.wildcard path none) (by simpa using finished)
  | some clause =>
      exact finishImport_keepsStartByte start clause.span
        (.wildcard path (some clause)) (by simpa using finished)

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

theorem selectiveImport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow
      (ImportInternals.selectiveImport start) := by
  unfold ImportInternals.selectiveImport
  apply Parser.bind_preservesTokenWindow selectedImports_preservesTokenWindow
  intro selection
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .from .importDecl)
  intro fromMarker
  apply Parser.bind_preservesTokenWindow
    (modulePath_preservesTokenWindow .importDecl)
  intro path
  apply Parser.bind_preservesTokenWindow optionalHiding_preservesTokenWindow
  intro hidden
  exact finishImport_preservesTokenWindow start
    (match hidden with | some clause => clause.span | none => path.span)
    (.selected selection path hidden)

theorem selectiveImport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess
      (ImportInternals.selectiveImport start) := by
  unfold ImportInternals.selectiveImport
  apply Parser.bind_cursorMonotoneOnSuccess
    selectedImports_cursorMonotoneOnSuccess
  intro selection
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .from .importDecl)
  intro fromMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (modulePath_cursorMonotoneOnSuccess .importDecl)
  intro path
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalHiding_cursorMonotoneOnSuccess
  intro hidden
  exact finishImport_cursorMonotoneOnSuccess start
    (match hidden with | some clause => clause.span | none => path.span)
    (.selected selection path hidden)

theorem selectiveImport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ImportDecl}
    (parsed : ImportInternals.selectiveImport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ImportInternals.selectiveImport at parsed
  rcases importBind_ok_components parsed with
    ⟨selection, afterSelection, _selectionResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨fromMarker, afterFrom, _fromResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨path, afterPath, _pathResult, rest⟩
  rcases importBind_ok_components rest with
    ⟨hidden, afterHidden, _hiddenResult, finished⟩
  cases hidden with
  | none =>
      exact finishImport_keepsStartByte start path.span
        (.selected selection path none) (by simpa using finished)
  | some clause =>
      exact finishImport_keepsStartByte start clause.span
        (.selected selection path (some clause)) (by simpa using finished)

/-- Complete import parsing preserves every ordinary token window. -/
theorem importDecl_preservesTokenWindow :
    Parser.PreservesTokenWindow importDecl := by
  unfold importDecl
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .importKw .importDecl)
  intro importKeyword
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact namespaceImport_preservesTokenWindow importKeyword.span
    · simp only [namespaceAlias]
      exact wildcardImport_preservesTokenWindow importKeyword.span
  · simp only [star]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact selectiveImport_preservesTokenWindow importKeyword.span
    · simp only [selected]
      exact plainImport_preservesTokenWindow importKeyword.span

theorem importDecl_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess importDecl :=
  importDecl_preservesTokenWindow.preservesTokensOnSuccess

/-- Complete import parsing never rewinds the parser cursor. -/
theorem importDecl_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess importDecl := by
  unfold importDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .importKw .importDecl)
  intro importKeyword
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases star : isSymbol observed .star
  · simp only [star, if_true]
    by_cases namespaceAlias :
        observed.peekOffsetKind? 1 == some (.keyword .asKw)
    · simp only [namespaceAlias, if_true]
      exact namespaceImport_cursorMonotoneOnSuccess importKeyword.span
    · simp only [namespaceAlias]
      exact wildcardImport_cursorMonotoneOnSuccess importKeyword.span
  · simp only [star]
    by_cases selected : isSymbol observed .leftBrace
    · simp only [selected, if_true]
      exact selectiveImport_cursorMonotoneOnSuccess importKeyword.span
    · simp only [selected]
      exact plainImport_cursorMonotoneOnSuccess importKeyword.span

/-- Complete import parsing starts at the leading `import` token. -/
theorem importDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess importDecl (·.span) := by
  unfold importDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .importKw) .importDecl (· == .keyword .importKw))
  intro importKeyword input result final parsed
  rcases importBind_ok_components parsed with
    ⟨observed, afterObserved, observedResult, branchResult⟩
  unfold getState at observedResult
  cases observedResult
  split at branchResult
  · split at branchResult
    · exact namespaceImport_keepsStartByte importKeyword.span branchResult
    · exact wildcardImport_keepsStartByte importKeyword.span branchResult
  · split at branchResult
    · exact selectiveImport_keepsStartByte importKeyword.span branchResult
    · exact plainImport_keepsStartByte importKeyword.span branchResult

end Solcore.Syntax.Parser
