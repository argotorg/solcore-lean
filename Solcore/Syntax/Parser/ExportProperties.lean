import Solcore.Syntax.Parser.Export
import Solcore.Syntax.Parser.PrimitiveCarrierProperties

/-! Provenance, token-window, and cursor contracts for export subparsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem exportBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
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

private theorem getState_preservesExportTokenWindow :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

private theorem exportPathTail_validFor (first : Identifier) :
    ∀ fuel last tailRev state firstIndex firstToken,
      state.ValidFor →
      first.span.ValidFor state.file →
      last.span.ValidFor state.file →
      (∀ component ∈ tailRev, component.span.ValidFor state.file) →
      first.span.startByte ≤ last.span.endByte →
      state.tokens[firstIndex]? = some firstToken →
      firstToken.span = first.span →
      firstIndex < state.cursor →
      (ExportInternals.exportPathTail first fuel last tailRev state).ValidFor
        state QualifiedName.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      unfold ExportInternals.exportPathTail
      split
      · cases dotResult : symbol .dot .exportDecl state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have dotValid := symbol_validFor .dot .exportDecl state stateValid
            rw [dotResult] at dotValid
            simpa only [Reply.ValidFor] using dotValid
        | ok dot afterDot =>
            have dotValid := symbol_validFor .dot .exportDecl state stateValid
            rw [dotResult] at dotValid
            have dotShape := symbol_ok_state_shape .dot .exportDecl dotResult
            simp only
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have componentValid := identifier_validFor .exportDecl
                  afterDot dotValid.2.1
                rw [componentResult] at componentValid
                simpa only [Reply.ValidFor] using
                  componentValid.of_file_eq dotValid.2.2
            | ok component next =>
                have componentValid := identifier_validFor .exportDecl
                  afterDot dotValid.2.1
                rw [componentResult] at componentValid
                rcases identifier_ok_state_shape .exportDecl componentResult with
                  ⟨componentToken, componentFound, componentSpan,
                    componentTokens, componentCursor⟩
                have componentFoundInState :
                    state.tokens[state.cursor + 1]? = some componentToken := by
                  have foundAtCursor :=
                    State.getElem?_eq_some_of_peek?_eq_some componentFound
                  simpa [dotShape.2] using foundAtCursor
                have firstBeforeComponentIndex :
                    firstIndex < state.cursor + 1 :=
                  Nat.lt_of_lt_of_le firstBeforeCursor
                    (Nat.le_add_right state.cursor 1)
                have firstEndBeforeComponentStart :
                    first.span.endByte ≤ component.span.startByte := by
                  have ordered :=
                    stateValid.token_end_le_token_start_of_getElem?_lt
                      firstFound componentFoundInState
                      firstBeforeComponentIndex
                  simpa [firstSpan, componentSpan] using ordered
                have firstBeforeComponent :
                    first.span.startByte ≤ component.span.endByte := by
                  apply Nat.le_trans firstValid.2.1
                  apply Nat.le_trans firstEndBeforeComponentStart
                  have spanValid : component.span.ValidFor afterDot.file := by
                    simpa only [Located.ValidFor] using componentValid.1
                  exact spanValid.2.1
                have firstValidNext : first.span.ValidFor next.file := by
                  simpa [componentValid.2.2, dotValid.2.2] using firstValid
                have componentValidNext :
                    component.span.ValidFor next.file := by
                  have spanValid : component.span.ValidFor afterDot.file := by
                    simpa only [Located.ValidFor] using componentValid.1
                  simpa [componentValid.2.2] using spanValid
                have tailValidNext : ∀ item ∈ component :: tailRev,
                    item.span.ValidFor next.file := by
                  intro item member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact componentValidNext
                  · simpa [componentValid.2.2, dotValid.2.2] using
                      tailValid item member
                have firstFoundNext :
                    next.tokens[firstIndex]? = some firstToken := by
                  simpa [componentTokens, dotShape.2] using firstFound
                have firstBeforeNextCursor : firstIndex < next.cursor := by
                  have firstBeforeAfterDot : firstIndex < afterDot.cursor := by
                    rw [dotShape.2]
                    exact Nat.lt_of_lt_of_le firstBeforeCursor
                      (Nat.le_add_right state.cursor 1)
                  rw [componentCursor]
                  exact Nat.lt_of_lt_of_le firstBeforeAfterDot
                    (Nat.le_add_right afterDot.cursor 1)
                exact (inductionHypothesis component (component :: tailRev)
                  next firstIndex firstToken componentValid.2.1
                  firstValidNext componentValidNext tailValidNext
                  firstBeforeComponent firstFoundNext firstSpan
                  firstBeforeNextCursor).of_file_eq
                    (componentValid.2.2.trans dotValid.2.2)
      · unfold ExportInternals.finishExportPath Reply.ValidFor
          QualifiedName.ValidFor
        refine ⟨⟨?_, ?_⟩, stateValid, rfl⟩
        · exact SourceSpan.cover_validFor firstValid lastValid
            firstBeforeLast
        · intro component member
          simp only [NonemptyList.toList, List.mem_cons,
            List.mem_reverse] at member
          rcases member with rfl | member
          · exact firstValid
          · exact tailValid component member

/-- Export paths preserve every retained component and their covering span. -/
theorem exportPath_validFor :
    ExportInternals.exportPath.ValidFor QualifiedName.ValidFor := by
  intro input inputValid
  unfold ExportInternals.exportPath
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have firstValid := identifier_validFor .exportDecl input inputValid
      rw [firstResult] at firstValid
      simpa only [Reply.ValidFor] using firstValid
  | ok first next =>
      have firstValid := identifier_validFor .exportDecl input inputValid
      rw [firstResult] at firstValid
      rcases identifier_ok_state_shape .exportDecl firstResult with
        ⟨firstToken, firstFound, firstSpan, firstTokens, firstCursor⟩
      have firstFoundNext :
          next.tokens[input.cursor]? = some firstToken := by
        have foundAtCursor :=
          State.getElem?_eq_some_of_peek?_eq_some firstFound
        simpa [firstTokens] using foundAtCursor
      have firstValidNext : first.span.ValidFor next.file := by
        have spanValid : first.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using firstValid.1
        simpa [firstValid.2.2] using spanValid
      exact (exportPathTail_validFor first (next.remainingCount + 1)
        first [] next input.cursor firstToken firstValid.2.1
        firstValidNext firstValidNext (by simp) firstValidNext.2.1
        firstFoundNext firstSpan (by rw [firstCursor]; simp)).of_file_eq
          firstValid.2.2

private theorem exportPathTail_preservesTokenWindow (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.PreservesTokenWindow
        (ExportInternals.exportPathTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold ExportInternals.exportPathTail
      split
      · have dotShape := symbol_preservesTokenWindow .dot .exportDecl input
        cases dotResult : symbol .dot .exportDecl input with
        | invariant error =>
            simp only [Reply.PreservesTokenWindow]
        | reject failure rejected =>
            rw [dotResult] at dotShape
            simpa only [Reply.PreservesTokenWindow] using dotShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            simp only
            have componentShape :=
              identifier_preservesTokenWindow .exportDecl afterDot
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error =>
                simp only [Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [componentResult] at componentShape
                simpa only [Reply.PreservesTokenWindow] using
                  componentShape.trans dotShape
            | ok component afterComponent =>
                rw [componentResult] at componentShape
                simpa only using (inductionHypothesis component
                    (component :: tailRev) afterComponent).trans
                  (componentShape.trans dotShape)
      · unfold ExportInternals.finishExportPath
        exact ⟨rfl, rfl⟩

/-- Export paths preserve their immutable token carrier and active window. -/
theorem exportPath_preservesTokenWindow :
    Parser.PreservesTokenWindow ExportInternals.exportPath := by
  intro input
  unfold ExportInternals.exportPath
  have firstShape := identifier_preservesTokenWindow .exportDecl input
  cases firstResult : identifier .exportDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first afterFirst =>
      rw [firstResult] at firstShape
      exact (exportPathTail_preservesTokenWindow first
        (afterFirst.remainingCount + 1) first [] afterFirst).trans firstShape

/-- Successful export paths retain the immutable lexer token carrier. -/
theorem exportPath_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ExportInternals.exportPath :=
  exportPath_preservesTokenWindow.preservesTokensOnSuccess

private theorem exportPathTail_keepsFirstStart (first : Identifier) :
    ∀ fuel last tailRev input path next,
      ExportInternals.exportPathTail first fuel last tailRev input =
          .ok path next →
        path.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result
      unfold ExportInternals.exportPathTail at result
      split at result
      · cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact inductionHypothesis component (component :: tailRev)
                  afterComponent path next result
      · unfold ExportInternals.finishExportPath at result
        cases result
        rfl

/-- An export path starts at the first identifier token that it retains. -/
theorem exportPath_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.exportPath (·.span) := by
  intro input path next result
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      rcases identifier_ok_state_shape .exportDecl firstResult with
        ⟨token, found, tokenSpan, _tokens, _cursor⟩
      refine ⟨token, found, ?_⟩
      rw [tokenSpan]
      exact (exportPathTail_keepsFirstStart first
        (afterFirst.remainingCount + 1) first [] afterFirst path next
        result).symm

private theorem exportPathTail_cursorMonotoneOnSuccess
    (first : Identifier) : ∀ fuel last tailRev,
      Parser.CursorMonotoneOnSuccess
        (ExportInternals.exportPathTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result
      unfold ExportInternals.exportPathTail at result
      split at result
      · cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact Nat.le_trans
                  (symbol_cursorMonotoneOnSuccess .dot .exportDecl
                    input dot afterDot dotResult)
                  (Nat.le_trans
                    (identifier_cursorMonotoneOnSuccess .exportDecl
                      afterDot component afterComponent componentResult)
                    (inductionHypothesis component (component :: tailRev)
                      afterComponent path next result))
      · unfold ExportInternals.finishExportPath at result
        cases result
        exact Nat.le_refl _

/-- Successful export-path parsing never rewinds the parser cursor. -/
theorem exportPath_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ExportInternals.exportPath := by
  intro input path next result
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact Nat.le_trans
        (identifier_cursorMonotoneOnSuccess .exportDecl
          input first afterFirst firstResult)
        (exportPathTail_cursorMonotoneOnSuccess first
          (afterFirst.remainingCount + 1) first [] afterFirst path next result)

private theorem starConstructorSelection_validFor :
    (do
      let opening ← symbol .leftParen .exportDecl
      let marker ← symbol .star .exportDecl
      let closing ← symbol .rightParen .exportDecl
      pure ({
        span := SourceSpan.cover opening.span closing.span
        value := ConstructorSelectionValue.all marker.span
      } : ConstructorSelection)).ValidFor ConstructorSelection.ValidFor := by
  let parser : Parser ConstructorSelection := do
    let opening ← symbol .leftParen .exportDecl
    let marker ← symbol .star .exportDecl
    let closing ← symbol .rightParen .exportDecl
    pure {
      span := SourceSpan.cover opening.span closing.span
      value := .all marker.span
    }
  change parser.ValidFor ConstructorSelection.ValidFor
  have weak : parser.ValidFor (fun _ _ => True) := by
    dsimp [parser]
    apply Parser.bind_validFor (symbol_validFor .leftParen .exportDecl)
    intro opening
    apply Parser.bind_validFor (symbol_validFor .star .exportDecl)
    intro marker
    apply Parser.bind_validFor (symbol_validFor .rightParen .exportDecl)
    intro closing
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : parser input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok selection final =>
      rw [parsed] at weakResult
      have stages := parsed
      dsimp [parser] at stages
      rcases exportBind_ok_components stages with
        ⟨opening, afterOpening, openingResult, rest⟩
      rcases exportBind_ok_components rest with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases exportBind_ok_components rest with
        ⟨closing, afterClosing, closingResult, finished⟩
      have openingValid := symbol_validFor .leftParen .exportDecl
        input inputValid
      rw [openingResult] at openingValid
      have markerValid := symbol_validFor .star .exportDecl
        afterOpening openingValid.2.1
      rw [markerResult] at markerValid
      have closingValid := symbol_validFor .rightParen .exportDecl
        afterMarker markerValid.2.1
      rw [closingResult] at closingValid
      have openingSpanValid : opening.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using openingValid.1
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor, openingValid.2.2] using markerValid.1
      have closingSpanValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor, markerValid.2.2,
          openingValid.2.2] using closingValid.1
      have openingShape := symbol_ok_state_shape .leftParen .exportDecl
        openingResult
      have closingShape := symbol_ok_state_shape .rightParen .exportDecl
        closingResult
      have openingAt :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have closingAtAfterMarker :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have closingAtInput :
          input.tokens[afterMarker.cursor]? = some closing := by
        have openingTokens := symbol_preservesTokensOnSuccess
          .leftParen .exportDecl input opening afterOpening openingResult
        have markerTokens := symbol_preservesTokensOnSuccess
          .star .exportDecl afterOpening marker afterMarker markerResult
        simpa [markerTokens, openingTokens] using closingAtAfterMarker
      have cursorOrder : input.cursor < afterMarker.cursor :=
        Nat.lt_trans
          (acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .exportDecl
            (· == .symbol .leftParen) openingResult)
          (acceptToken_cursor_lt_onSuccess (.symbol .star) .exportDecl
            (· == .symbol .star) markerResult)
      have openingBeforeClosing :=
        inputValid.token_end_le_token_start_of_getElem?_lt
          openingAt closingAtInput cursorOrder
      have outerValid := SourceSpan.cover_validFor openingSpanValid
        closingSpanValid (Nat.le_trans openingSpanValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1))
      cases finished
      exact ⟨⟨outerValid, markerSpanValid⟩,
        weakResult.2.1, weakResult.2.2⟩

private theorem namedConstructorSelection_validFor :
    (do
      let values ← delimitedNoTrailing .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel
      let constructors ← ExportInternals.requireConstructorNames values
      pure ({
        span := values.span
        value := ConstructorSelectionValue.named constructors
      } : ConstructorSelection)).ValidFor ConstructorSelection.ValidFor := by
  apply Parser.bind_validFor_of_value
    (delimitedNoTrailing_validFor Located.ValidFor .leftParen .rightParen
      false (identifier .exportDecl) .exportDecl .topLevel
      (identifier_validFor .exportDecl)
      (identifier_preservesTokensOnSuccess .exportDecl))
  intro values input inputValid valuesValid
  unfold ExportInternals.requireConstructorNames
  cases elements : values.elements with
  | nil => trivial
  | cons head tail =>
      simp only [bind, pure, Reply.ValidFor,
        ConstructorSelection.ValidFor]
      refine ⟨⟨valuesValid.1, ?_⟩, inputValid, trivial⟩
      intro constructor member
      exact valuesValid.2 constructor (by
        simpa [NonemptyList.toList, elements] using member)

/-- Constructor selections retain their delimiter, marker, and name ranges. -/
theorem constructorSelection_validFor :
    ExportInternals.constructorSelection.ValidFor
      ConstructorSelection.ValidFor := by
  unfold ExportInternals.constructorSelection
  apply Parser.bind_validFor getState_validFor
  intro observed
  split
  · exact starConstructorSelection_validFor
  · exact namedConstructorSelection_validFor

private theorem requireConstructorNames_preservesTokenWindow
    (values : DelimitedList Identifier) :
    Parser.PreservesTokenWindow
      (ExportInternals.requireConstructorNames values) := by
  intro input
  unfold ExportInternals.requireConstructorNames
  cases values.elements <;> trivial

/-- Constructor selections preserve every ordinary token window. -/
theorem constructorSelection_preservesTokenWindow :
    Parser.PreservesTokenWindow
      ExportInternals.constructorSelection := by
  unfold ExportInternals.constructorSelection
  apply Parser.bind_preservesTokenWindow getState_preservesExportTokenWindow
  intro observed
  split
  · apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .leftParen .exportDecl)
    intro opening
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .star .exportDecl)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .rightParen .exportDecl)
    intro closing
    exact Parser.pure_preservesTokenWindow _
  · apply Parser.bind_preservesTokenWindow
      (delimitedWithPolicy_preservesTokenWindow .leftParen .rightParen false
        false (identifier .exportDecl) .exportDecl .topLevel
        (identifier_preservesTokenWindow .exportDecl))
    intro values
    apply Parser.bind_preservesTokenWindow
      (requireConstructorNames_preservesTokenWindow values)
    intro constructors
    exact Parser.pure_preservesTokenWindow _

/-- Successful constructor selections retain the lexer token carrier. -/
theorem constructorSelection_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess
      ExportInternals.constructorSelection :=
  constructorSelection_preservesTokenWindow.preservesTokensOnSuccess

private theorem requireConstructorNames_cursorMonotoneOnSuccess
    (values : DelimitedList Identifier) :
    Parser.CursorMonotoneOnSuccess
      (ExportInternals.requireConstructorNames values) := by
  intro input constructors next parsed
  unfold ExportInternals.requireConstructorNames at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      exact Nat.le_refl _

/-- Successful constructor selections never rewind the cursor. -/
theorem constructorSelection_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess
      ExportInternals.constructorSelection := by
  unfold ExportInternals.constructorSelection
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .leftParen .exportDecl)
    intro opening
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .star .exportDecl)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .rightParen .exportDecl)
    intro closing
    exact Parser.pure_cursorMonotoneOnSuccess _
  · apply Parser.bind_cursorMonotoneOnSuccess
      (delimitedNoTrailing_cursorMonotoneOnSuccess .leftParen .rightParen
        false (identifier .exportDecl) .exportDecl .topLevel)
    intro values
    apply Parser.bind_cursorMonotoneOnSuccess
      (requireConstructorNames_cursorMonotoneOnSuccess values)
    intro constructors
    exact Parser.pure_cursorMonotoneOnSuccess _

private theorem starConstructorSelection_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess (do
      let opening ← symbol .leftParen .exportDecl
      let marker ← symbol .star .exportDecl
      let closing ← symbol .rightParen .exportDecl
      pure ({
        span := SourceSpan.cover opening.span closing.span
        value := ConstructorSelectionValue.all marker.span
      } : ConstructorSelection)) (·.span) := by
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (symbol_startsAtCurrentTokenOnSuccess .leftParen .exportDecl)
  intro opening input selection final parsed
  rcases exportBind_ok_components parsed with
    ⟨marker, afterMarker, _markerResult, rest⟩
  rcases exportBind_ok_components rest with
    ⟨closing, afterClosing, _closingResult, finished⟩
  cases finished
  rfl

private theorem namedConstructorSelection_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess (do
      let values ← delimitedNoTrailing .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel
      let constructors ← ExportInternals.requireConstructorNames values
      pure ({
        span := values.span
        value := ConstructorSelectionValue.named constructors
      } : ConstructorSelection)) (·.span) := by
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimitedNoTrailing_startsAtCurrentTokenOnSuccess .leftParen .rightParen
      false (identifier .exportDecl) .exportDecl .topLevel)
  intro values input selection final parsed
  rcases exportBind_ok_components parsed with
    ⟨constructors, afterConstructors, _constructorsResult, finished⟩
  cases finished
  rfl

/-- A constructor selection starts at its opening parenthesis. -/
theorem constructorSelection_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.constructorSelection (·.span) := by
  intro input selection final parsed
  unfold ExportInternals.constructorSelection at parsed
  simp only [getState, bind] at parsed
  split at parsed
  · exact starConstructorSelection_startsAtCurrentTokenOnSuccess
      input selection final parsed
  · exact namedConstructorSelection_startsAtCurrentTokenOnSuccess
      input selection final parsed

/-- Export names retain every marker, identifier, and constructor range. -/
theorem exportName_validFor :
    ExportInternals.exportName.ValidFor ExportName.ValidFor := by
  intro input inputValid
  unfold ExportInternals.exportName
  split
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have markerValid := symbol_validFor .star .exportDecl input inputValid
        rw [markerResult] at markerValid
        simpa only [Reply.ValidFor] using markerValid
    | ok marker next =>
        have markerValid := symbol_validFor .star .exportDecl input inputValid
        rw [markerResult] at markerValid
        simp only [Reply.ValidFor, ExportName.ValidFor]
        exact ⟨⟨by simpa only [Located.ValidFor] using markerValid.1,
          by simpa only [Located.ValidFor] using markerValid.1⟩,
          markerValid.2.1, markerValid.2.2⟩
  · split
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have selectedValid := operatorSelector_validFor .exportDecl
            input inputValid
          rw [selectedResult] at selectedValid
          simpa only [Reply.ValidFor] using selectedValid
      | ok selected next =>
          have selectedValid := operatorSelector_validFor .exportDecl
            input inputValid
          rw [selectedResult] at selectedValid
          cases selectedValue : selected.value with
          | identifier name => simp only [selectedValue, Reply.ValidFor]
          | operator spelling =>
              simp only [selectedValue, Reply.ValidFor, ExportName.ValidFor]
              exact ⟨⟨selectedValid.1.1, selectedValid.1.1⟩,
                selectedValid.2.1, selectedValid.2.2⟩
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have nameValid := identifier_validFor .exportDecl input inputValid
          rw [nameResult] at nameValid
          simpa only [Reply.ValidFor] using nameValid
      | ok name afterName =>
          have nameValid := identifier_validFor .exportDecl input inputValid
          rw [nameResult] at nameValid
          have nameSpanValid : name.span.ValidFor input.file := by
            simpa only [Located.ValidFor] using nameValid.1
          simp only
          split
          · cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have constructorsValid := constructorSelection_validFor
                  afterName nameValid.2.1
                rw [constructorsResult] at constructorsValid
                simpa only [Reply.ValidFor] using
                  constructorsValid.of_file_eq nameValid.2.2
            | ok constructors next =>
                have constructorsValid := constructorSelection_validFor
                  afterName nameValid.2.1
                rw [constructorsResult] at constructorsValid
                have constructorsValidInput :
                    ConstructorSelection.ValidFor input.file constructors := by
                  simpa [nameValid.2.2] using constructorsValid.1
                rcases identifier_ok_state_shape .exportDecl nameResult with
                  ⟨nameToken, nameFound, nameTokenSpan, nameTokens,
                    nameCursor⟩
                rcases constructorSelection_startsAtCurrentTokenOnSuccess
                    afterName constructors next constructorsResult with
                  ⟨opening, openingFound, openingStart⟩
                have nameAt :=
                  State.getElem?_eq_some_of_peek?_eq_some nameFound
                have openingAtAfterName :=
                  State.getElem?_eq_some_of_peek?_eq_some openingFound
                have openingAtInput :
                    input.tokens[afterName.cursor]? = some opening := by
                  simpa [nameTokens] using openingAtAfterName
                have nameBeforeOpening :=
                  inputValid.token_end_le_token_start_of_getElem?_lt
                    nameAt openingAtInput (by rw [nameCursor]; simp)
                have ordered : name.span.startByte ≤ constructors.span.endByte :=
                  Nat.le_trans nameSpanValid.2.1 (Nat.le_trans
                    (by simpa [nameTokenSpan] using nameBeforeOpening)
                    (by rw [openingStart]; exact constructorsValidInput.1.2.1))
                have outerValid := SourceSpan.cover_validFor nameSpanValid
                  constructorsValidInput.1 ordered
                simp only [Reply.ValidFor, ExportName.ValidFor]
                refine ⟨⟨outerValid, nameSpanValid, ?_⟩,
                  constructorsValid.2.1,
                  constructorsValid.2.2.trans nameValid.2.2⟩
                intro retained member
                have retainedEq : retained = constructors := by
                  simpa using member.symm
                subst retained
                exact constructorsValidInput
          · simp only [Reply.ValidFor, ExportName.ValidFor]
            exact ⟨⟨nameSpanValid, nameSpanValid, by simp⟩,
              nameValid.2.1, nameValid.2.2⟩

/-- Export-name parsing preserves every ordinary token window. -/
theorem exportName_preservesTokenWindow :
    Parser.PreservesTokenWindow ExportInternals.exportName := by
  intro input
  unfold ExportInternals.exportName
  split
  · have markerShape := symbol_preservesTokenWindow .star .exportDecl input
    cases markerResult : symbol .star .exportDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [markerResult] at markerShape
        exact markerShape
    | ok marker next =>
        rw [markerResult] at markerShape
        exact markerShape
  · split
    · have selectedShape :=
        operatorSelector_preservesTokenWindow .exportDecl input
      cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => trivial
      | reject failure rejected =>
          rw [selectedResult] at selectedShape
          exact selectedShape
      | ok selected next =>
          rw [selectedResult] at selectedShape
          cases selectedValue : selected.value with
          | identifier name =>
              simp only [selectedValue, Reply.PreservesTokenWindow]
          | operator spelling =>
              simpa only [selectedValue, Reply.PreservesTokenWindow] using
                selectedShape
    · have nameShape := identifier_preservesTokenWindow .exportDecl input
      cases nameResult : identifier .exportDecl input with
      | invariant error => trivial
      | reject failure rejected =>
          rw [nameResult] at nameShape
          exact nameShape
      | ok name afterName =>
          rw [nameResult] at nameShape
          simp only
          split
          · have constructorsShape :=
              constructorSelection_preservesTokenWindow afterName
            cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => trivial
            | reject failure rejected =>
                rw [constructorsResult] at constructorsShape
                exact constructorsShape.trans nameShape
            | ok constructors next =>
                rw [constructorsResult] at constructorsShape
                exact constructorsShape.trans nameShape
          · exact nameShape

/-- Successful export names retain the immutable lexer token carrier. -/
theorem exportName_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ExportInternals.exportName :=
  exportName_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful export-name parsing never rewinds the cursor. -/
theorem exportName_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ExportInternals.exportName := by
  intro input exported next parsed
  unfold ExportInternals.exportName at parsed
  split at parsed
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at parsed
    | reject failure rejected => simp [markerResult] at parsed
    | ok marker afterMarker =>
        simp only [markerResult] at parsed
        cases parsed
        exact symbol_cursorMonotoneOnSuccess .star .exportDecl
          input marker next markerResult
  · split at parsed
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectedResult] at parsed
      | reject failure rejected => simp [selectedResult] at parsed
      | ok selected afterSelected =>
          simp only [selectedResult] at parsed
          cases selectedValue : selected.value with
          | identifier name => simp [selectedValue] at parsed
          | operator spelling =>
            simp only [selectedValue] at parsed
            cases parsed
            exact operatorSelector_cursorMonotoneOnSuccess .exportDecl
              input selected next selectedResult
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at parsed
      | reject failure rejected => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          split at parsed
          · cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp [constructorsResult] at parsed
            | reject failure rejected => simp [constructorsResult] at parsed
            | ok constructors afterConstructors =>
                simp only [constructorsResult] at parsed
                cases parsed
                exact Nat.le_trans
                  (identifier_cursorMonotoneOnSuccess .exportDecl
                    input name afterName nameResult)
                  (constructorSelection_cursorMonotoneOnSuccess
                    afterName constructors next constructorsResult)
          · cases parsed
            exact identifier_cursorMonotoneOnSuccess .exportDecl
              input name next nameResult

/-- An export name starts at its wildcard, operator, or identifier token. -/
theorem exportName_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.exportName (·.span) := by
  intro input exported next parsed
  unfold ExportInternals.exportName at parsed
  split at parsed
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at parsed
    | reject failure rejected => simp [markerResult] at parsed
    | ok marker afterMarker =>
        simp only [markerResult] at parsed
        cases parsed
        exact symbol_startsAtCurrentTokenOnSuccess .star .exportDecl
          input marker next markerResult
  · split at parsed
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectedResult] at parsed
      | reject failure rejected => simp [selectedResult] at parsed
      | ok selected afterSelected =>
          simp only [selectedResult] at parsed
          cases selectedValue : selected.value with
          | identifier name => simp [selectedValue] at parsed
          | operator spelling =>
            simp only [selectedValue] at parsed
            cases parsed
            exact operatorSelector_startsAtCurrentTokenOnSuccess .exportDecl
              input selected next selectedResult
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at parsed
      | reject failure rejected => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          rcases identifier_ok_state_shape .exportDecl nameResult with
            ⟨token, found, tokenSpan, _tokens, _cursor⟩
          split at parsed
          · cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp [constructorsResult] at parsed
            | reject failure rejected => simp [constructorsResult] at parsed
            | ok constructors afterConstructors =>
                simp only [constructorsResult] at parsed
                cases parsed
                exact ⟨token, found, by
                  simp [SourceSpan.cover, tokenSpan]⟩
          · cases parsed
            exact ⟨token, found, congrArg SourceSpan.startByte tokenSpan⟩

/-- Local export items retain their name or module-wildcard ranges. -/
theorem localExportItem_validFor :
    ExportInternals.localExportItem.ValidFor LocalExportItem.ValidFor := by
  intro input inputValid
  unfold ExportInternals.localExportItem
  split
  · cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have pathValid := exportPath_validFor input inputValid
        rw [pathResult] at pathValid
        simpa only [Reply.ValidFor] using pathValid
    | ok path afterPath =>
        have pathValid := exportPath_validFor input inputValid
        rw [pathResult] at pathValid
        simp only
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have dotValid := symbol_validFor .dot .exportDecl afterPath
              pathValid.2.1
            rw [dotResult] at dotValid
            simpa only [Reply.ValidFor] using
              dotValid.of_file_eq pathValid.2.2
        | ok dot afterDot =>
            have dotValid := symbol_validFor .dot .exportDecl afterPath
              pathValid.2.1
            rw [dotResult] at dotValid
            simp only
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have markerValid := symbol_validFor .star .exportDecl
                  afterDot dotValid.2.1
                rw [markerResult] at markerValid
                simpa only [Reply.ValidFor] using markerValid.of_file_eq
                  (dotValid.2.2.trans pathValid.2.2)
            | ok marker next =>
                have markerValid := symbol_validFor .star .exportDecl
                  afterDot dotValid.2.1
                rw [markerResult] at markerValid
                have markerSpanValid : marker.span.ValidFor input.file := by
                  simpa only [Located.ValidFor, dotValid.2.2,
                    pathValid.2.2] using markerValid.1
                rcases exportPath_startsAtCurrentTokenOnSuccess
                    input path afterPath pathResult with
                  ⟨firstToken, firstFound, firstStart⟩
                have firstAt :=
                  State.getElem?_eq_some_of_peek?_eq_some firstFound
                have markerShape := symbol_ok_state_shape .star .exportDecl
                  markerResult
                have markerAtAfterDot :=
                  State.getElem?_eq_some_of_peek?_eq_some markerShape.1
                have pathTokens := exportPath_preservesTokensOnSuccess
                  input path afterPath pathResult
                have dotTokens := symbol_preservesTokensOnSuccess .dot
                  .exportDecl afterPath dot afterDot dotResult
                have markerAtInput :
                    input.tokens[afterDot.cursor]? = some marker := by
                  simpa [dotTokens, pathTokens] using markerAtAfterDot
                have firstBeforeMarker :=
                  inputValid.token_end_le_token_start_of_getElem?_lt
                    firstAt markerAtInput (Nat.lt_of_le_of_lt
                      (exportPath_cursorMonotoneOnSuccess
                        input path afterPath pathResult)
                      (acceptToken_cursor_lt_onSuccess (.symbol .dot)
                        .exportDecl (· == .symbol .dot) dotResult))
                have firstSpanValid :=
                  inputValid.peek?_span_validFor firstFound
                have ordered : path.span.startByte ≤ marker.span.endByte := by
                  calc
                    path.span.startByte = firstToken.span.startByte :=
                      firstStart.symm
                    _ ≤ firstToken.span.endByte := firstSpanValid.2.1
                    _ ≤ marker.span.startByte := firstBeforeMarker
                    _ ≤ marker.span.endByte := markerSpanValid.2.1
                have outerValid := SourceSpan.cover_validFor pathValid.1.1
                  markerSpanValid ordered
                simp only [Reply.ValidFor, LocalExportItem.ValidFor]
                exact ⟨⟨outerValid, pathValid.1, markerSpanValid⟩,
                  markerValid.2.1, markerValid.2.2.trans
                    (dotValid.2.2.trans pathValid.2.2)⟩
  · cases nameResult : ExportInternals.exportName input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have nameValid := exportName_validFor input inputValid
        rw [nameResult] at nameValid
        simpa only [Reply.ValidFor] using nameValid
    | ok name next =>
        have nameValid := exportName_validFor input inputValid
        rw [nameResult] at nameValid
        simp only [Reply.ValidFor, LocalExportItem.ValidFor]
        exact ⟨⟨nameValid.1.1, nameValid.1⟩,
          nameValid.2.1, nameValid.2.2⟩

/-- Local export items preserve every ordinary token window. -/
theorem localExportItem_preservesTokenWindow :
    Parser.PreservesTokenWindow ExportInternals.localExportItem := by
  intro input
  unfold ExportInternals.localExportItem
  split
  · have pathShape := exportPath_preservesTokenWindow input
    cases pathResult : ExportInternals.exportPath input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [pathResult] at pathShape
        exact pathShape
    | ok path afterPath =>
        rw [pathResult] at pathShape
        simp only
        have dotShape := symbol_preservesTokenWindow .dot .exportDecl afterPath
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => trivial
        | reject failure rejected =>
            rw [dotResult] at dotShape
            exact dotShape.trans pathShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            simp only
            have markerShape :=
              symbol_preservesTokenWindow .star .exportDecl afterDot
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => trivial
            | reject failure rejected =>
                rw [markerResult] at markerShape
                exact markerShape.trans (dotShape.trans pathShape)
            | ok marker next =>
                rw [markerResult] at markerShape
                exact markerShape.trans (dotShape.trans pathShape)
  · have nameShape := exportName_preservesTokenWindow input
    cases nameResult : ExportInternals.exportName input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [nameResult] at nameShape
        exact nameShape
    | ok name next =>
        rw [nameResult] at nameShape
        exact nameShape

/-- Successful local export items retain the lexer token carrier. -/
theorem localExportItem_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ExportInternals.localExportItem :=
  localExportItem_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful local export items never rewind the cursor. -/
theorem localExportItem_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ExportInternals.localExportItem := by
  intro input item next parsed
  unfold ExportInternals.localExportItem at parsed
  split at parsed
  · cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp [pathResult] at parsed
    | reject failure rejected => simp [pathResult] at parsed
    | ok path afterPath =>
        simp only [pathResult] at parsed
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at parsed
        | reject failure rejected => simp [dotResult] at parsed
        | ok dot afterDot =>
            simp only [dotResult] at parsed
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at parsed
            | reject failure rejected => simp [markerResult] at parsed
            | ok marker afterMarker =>
                simp only [markerResult] at parsed
                cases parsed
                exact Nat.le_trans
                  (exportPath_cursorMonotoneOnSuccess
                    input path afterPath pathResult)
                  (Nat.le_trans
                    (symbol_cursorMonotoneOnSuccess .dot .exportDecl
                      afterPath dot afterDot dotResult)
                    (symbol_cursorMonotoneOnSuccess .star .exportDecl
                      afterDot marker next markerResult))
  · cases nameResult : ExportInternals.exportName input with
    | invariant error => simp [nameResult] at parsed
    | reject failure rejected => simp [nameResult] at parsed
    | ok name afterName =>
        simp only [nameResult] at parsed
        cases parsed
        exact exportName_cursorMonotoneOnSuccess
          input name next nameResult

/-- A local export item starts at its module path or exported name. -/
theorem localExportItem_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.localExportItem (·.span) := by
  intro input item next parsed
  unfold ExportInternals.localExportItem at parsed
  split at parsed
  · cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp [pathResult] at parsed
    | reject failure rejected => simp [pathResult] at parsed
    | ok path afterPath =>
        simp only [pathResult] at parsed
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at parsed
        | reject failure rejected => simp [dotResult] at parsed
        | ok dot afterDot =>
            simp only [dotResult] at parsed
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at parsed
            | reject failure rejected => simp [markerResult] at parsed
            | ok marker afterMarker =>
                simp only [markerResult] at parsed
                cases parsed
                rcases exportPath_startsAtCurrentTokenOnSuccess
                    input path afterPath pathResult with
                  ⟨token, found, start⟩
                exact ⟨token, found, by
                  simpa [SourceSpan.cover] using start⟩
  · cases nameResult : ExportInternals.exportName input with
    | invariant error => simp [nameResult] at parsed
    | reject failure rejected => simp [nameResult] at parsed
    | ok name afterName =>
        simp only [nameResult] at parsed
        cases parsed
        exact exportName_startsAtCurrentTokenOnSuccess
          input name next nameResult

end Solcore.Syntax.Parser
