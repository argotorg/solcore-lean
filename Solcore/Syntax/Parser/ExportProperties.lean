import Solcore.Syntax.Parser.Export
import Solcore.Syntax.Parser.PrimitiveCarrierProperties

/-! Provenance, token-window, and cursor contracts for export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

end Solcore.Syntax.Parser
