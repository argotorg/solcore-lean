import Solcore.Syntax.Parser.Declarations
import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.Name
import Solcore.Syntax.Parser.TopLevel

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeriveTargetInternals

private theorem deriveComponent_validFor :
    deriveComponent.ValidFor Located.ValidFor := by
  intro input inputValid
  unfold deriveComponent
  cases found : input.peek? with
  | none =>
      change (rejectAt input { head := .identifier, tail := [] }
        .topItem).ValidFor input Located.ValidFor
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  | some token =>
      cases reserved : reservedDeriveKeyword? token.value with
      | none =>
          simp only [reserved]
          exact identifier_validFor .topItem input inputValid
      | some keywordValue =>
          simp only [reserved, Reply.ValidFor, Located.ValidFor]
          have tokenValid := inputValid.peek?_span_validFor found
          refine ⟨tokenValid, ?_, rfl⟩
          have advanced : input.advance? = some
              (token, { input with cursor := input.cursor + 1 }) := by
            simp [State.advance?, found]
          exact (inputValid.advance?_validFor advanced).emit_validFor _
            tokenValid

private theorem deriveComponent_ok_state_shape {input next : State}
    {name : Identifier} (result : deriveComponent input = .ok name next) :
    ∃ token, input.peek? = some token ∧ token.span = name.span ∧
      next.tokens = input.tokens ∧ next.cursor = input.cursor + 1 := by
  unfold deriveComponent at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      change rejectAt input { head := .identifier, tail := [] }
        .topItem = .ok name next at result
      unfold rejectAt at result
      contradiction
  | some token =>
      simp only [found] at result
      cases reserved : reservedDeriveKeyword? token.value with
      | none =>
          simp only [reserved] at result
          rcases identifier_ok_state_shape .topItem result with
            ⟨parsedToken, parsedFound, parsedSpan, tokens, cursor⟩
          exact ⟨parsedToken, by simpa [found] using parsedFound,
            parsedSpan, tokens, cursor⟩
      | some keywordValue =>
          simp only [reserved] at result
          cases result
          exact ⟨token, rfl, rfl, rfl, rfl⟩

private theorem deriveComponent_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess deriveComponent := by
  intro input name next result
  exact (deriveComponent_ok_state_shape result).choose_spec.2.2.1

private theorem deriveComponent_preservesTokenWindow :
    Parser.PreservesTokenWindow deriveComponent := by
  intro input
  unfold deriveComponent
  cases found : input.peek? with
  | none =>
      exact rejectAt_preservesTokenWindow input
        { head := .identifier, tail := [] } .topItem
  | some token =>
      simp only
      cases reserved : reservedDeriveKeyword? token.value with
      | none =>
          simp only
          exact identifier_preservesTokenWindow .topItem input
      | some keywordValue =>
          simp [Reply.PreservesTokenWindow, State.emit]

private theorem deriveComponent_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess deriveComponent := by
  intro input name next result
  rw [(deriveComponent_ok_state_shape result).choose_spec.2.2.2]
  exact Nat.le_add_right _ _

private theorem deriveTargetTail_validFor (first : Identifier) :
    ∀ fuel last tailRev state firstIndex firstToken,
      state.ValidFor → first.span.ValidFor state.file →
      last.span.ValidFor state.file →
      (∀ component ∈ tailRev, component.span.ValidFor state.file) →
      first.span.startByte ≤ last.span.endByte →
      state.tokens[firstIndex]? = some firstToken →
      firstToken.span = first.span → firstIndex < state.cursor →
      (deriveTargetTail first fuel last tailRev state).ValidFor state
        QualifiedName.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      unfold deriveTargetTail
      split
      · cases dotResult : symbol .dot .topItem state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have valid := symbol_validFor .dot .topItem state stateValid
            rw [dotResult] at valid
            simpa only [Reply.ValidFor] using valid
        | ok dot afterDot =>
            have dotValid := symbol_validFor .dot .topItem state stateValid
            rw [dotResult] at dotValid
            have dotShape := symbol_ok_state_shape .dot .topItem dotResult
            simp only
            cases componentResult : deriveComponent afterDot with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have valid := deriveComponent_validFor afterDot dotValid.2.1
                rw [componentResult] at valid
                exact valid.of_file_eq dotValid.2.2
            | ok component next =>
                have componentValid :=
                  deriveComponent_validFor afterDot dotValid.2.1
                rw [componentResult] at componentValid
                rcases deriveComponent_ok_state_shape componentResult with
                  ⟨componentToken, componentFound, componentSpan,
                    componentTokens, componentCursor⟩
                have componentFoundInState :
                    state.tokens[state.cursor + 1]? = some componentToken := by
                  have atCursor :=
                    State.getElem?_eq_some_of_peek?_eq_some componentFound
                  simpa [dotShape.2] using atCursor
                have firstEndBeforeComponentStart :
                    first.span.endByte ≤ component.span.startByte := by
                  have ordered := stateValid.token_end_le_token_start_of_getElem?_lt
                    firstFound componentFoundInState
                    (Nat.lt_of_lt_of_le firstBeforeCursor
                      (Nat.le_add_right state.cursor 1))
                  simpa [firstSpan, componentSpan] using ordered
                have componentSpanValid :
                    component.span.ValidFor next.file := by
                  have : component.span.ValidFor afterDot.file := by
                    simpa only [Located.ValidFor] using componentValid.1
                  simpa [componentValid.2.2] using this
                apply (inductionHypothesis component (component :: tailRev)
                  next firstIndex firstToken componentValid.2.1
                  (by simpa [componentValid.2.2, dotValid.2.2] using firstValid)
                  componentSpanValid _ _ _ firstSpan _).of_file_eq
                  (componentValid.2.2.trans dotValid.2.2)
                · intro item member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact componentSpanValid
                  · simpa [componentValid.2.2, dotValid.2.2] using
                      tailValid item member
                · exact Nat.le_trans firstValid.2.1
                    (Nat.le_trans firstEndBeforeComponentStart
                      componentSpanValid.2.1)
                · simpa [componentTokens, dotShape.2] using firstFound
                · have dotCursor : afterDot.cursor = state.cursor + 1 := by
                    rw [dotShape.2]
                  rw [componentCursor, dotCursor]
                  exact Nat.lt_trans
                    (Nat.lt_trans firstBeforeCursor (Nat.lt_succ_self _))
                    (Nat.lt_succ_self _)
      · unfold finishDeriveTarget Reply.ValidFor QualifiedName.ValidFor
        refine ⟨⟨SourceSpan.cover_validFor firstValid lastValid
          firstBeforeLast, ?_⟩, stateValid, rfl⟩
        intro component member
        simp only [NonemptyList.toList, List.mem_cons,
          List.mem_reverse] at member
        rcases member with rfl | member
        · exact firstValid
        · exact tailValid component member

/-- Derive-target parsing preserves its covering and component provenance. -/
theorem deriveTarget_validFor :
    deriveTarget.ValidFor QualifiedName.ValidFor := by
  intro input inputValid
  unfold deriveTarget
  cases firstResult : deriveComponent input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have valid := deriveComponent_validFor input inputValid
      rw [firstResult] at valid
      exact valid
  | ok first next =>
      have firstValid := deriveComponent_validFor input inputValid
      rw [firstResult] at firstValid
      rcases deriveComponent_ok_state_shape firstResult with
        ⟨firstToken, firstFound, firstSpan, firstTokens, firstCursor⟩
      have foundNext : next.tokens[input.cursor]? = some firstToken := by
        have atCursor := State.getElem?_eq_some_of_peek?_eq_some firstFound
        simpa [firstTokens] using atCursor
      have spanValid : first.span.ValidFor next.file := by
        have : first.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using firstValid.1
        simpa [firstValid.2.2] using this
      exact (deriveTargetTail_validFor first (next.remainingCount + 1)
        first [] next input.cursor firstToken firstValid.2.1 spanValid
        spanValid (by simp) spanValid.2.1 foundNext firstSpan
        (by rw [firstCursor]; simp)).of_file_eq firstValid.2.2

private theorem deriveTargetTail_ok_state_shape (first : Identifier) :
    ∀ fuel last tailRev input name next,
      deriveTargetTail first fuel last tailRev input = .ok name next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        name.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input name next result
      unfold deriveTargetTail at result
      split at result
      · cases dotResult : symbol .dot .topItem input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : deriveComponent afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have recursive := inductionHypothesis component
                  (component :: tailRev) afterComponent name next result
                have dotShape :=
                  symbol_ok_state_shape .dot .topItem dotResult
                rcases deriveComponent_ok_state_shape componentResult with
                  ⟨_token, _found, _span, componentTokens,
                    componentCursor⟩
                refine ⟨recursive.1.trans
                    (componentTokens.trans (by rw [dotShape.2])), ?_,
                  recursive.2.2⟩
                apply Nat.le_trans _ recursive.2.1
                rw [componentCursor, dotShape.2]
                exact Nat.le_trans (Nat.le_add_right input.cursor 1)
                  (Nat.le_add_right (input.cursor + 1) 1)
      · unfold finishDeriveTarget at result
        cases result
        exact ⟨rfl, Nat.le_refl _, rfl⟩

/--
Successful derive-target parsing begins at the first input token, preserves the
token carrier, and consumes at least that token.
-/
theorem deriveTarget_ok_state_shape {input next : State}
    {name : DeriveTarget} (result : deriveTarget input = .ok name next) :
    ∃ firstToken, input.peek? = some firstToken ∧
      firstToken.span.startByte = name.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold deriveTarget at result
  cases firstResult : deriveComponent input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have tailShape := deriveTargetTail_ok_state_shape first
        (afterFirst.remainingCount + 1) first [] afterFirst name next result
      rcases deriveComponent_ok_state_shape firstResult with
        ⟨firstToken, found, span, tokens, cursor⟩
      refine ⟨firstToken, found, ?_, tailShape.1.trans tokens, ?_⟩
      · exact (congrArg (fun sourceSpan : SourceSpan =>
          sourceSpan.startByte) span).trans tailShape.2.2.symm
      · exact Nat.lt_of_lt_of_le (by rw [cursor]; simp) tailShape.2.1

/-- Derive-target success preserves the immutable token carrier. -/
theorem deriveTarget_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess deriveTarget := by
  intro input name next result
  exact (deriveTarget_ok_state_shape result).choose_spec.2.2.1

private theorem deriveTargetTail_preservesTokenWindow
    (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.PreservesTokenWindow
        (deriveTargetTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold deriveTargetTail
      split
      · have dotShape := symbol_preservesTokenWindow .dot .topItem input
        cases dotResult : symbol .dot .topItem input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [dotResult] at dotShape
            exact dotShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            have componentShape :=
              deriveComponent_preservesTokenWindow afterDot
            cases componentResult : deriveComponent afterDot with
            | invariant error =>
                simp only [componentResult, Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [componentResult] at componentShape
                simpa only [componentResult,
                  Reply.PreservesTokenWindow] using
                    componentShape.trans dotShape
            | ok component next =>
                rw [componentResult] at componentShape
                simpa only [componentResult,
                  Reply.PreservesTokenWindow] using
                    (inductionHypothesis component
                      (component :: tailRev) next).trans
                        (componentShape.trans dotShape)
      · unfold finishDeriveTarget
        exact ⟨rfl, rfl⟩

/-- Derive targets preserve every ordinary token window. -/
theorem deriveTarget_preservesTokenWindow :
    Parser.PreservesTokenWindow deriveTarget := by
  intro input
  unfold deriveTarget
  have firstShape := deriveComponent_preservesTokenWindow input
  cases firstResult : deriveComponent input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first next =>
      rw [firstResult] at firstShape
      exact (deriveTargetTail_preservesTokenWindow first
        (next.remainingCount + 1) first [] next).trans firstShape

/-- Derive-target success never moves the cursor backwards. -/
theorem deriveTarget_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess deriveTarget := by
  intro input name next result
  exact Nat.le_of_lt
    (deriveTarget_ok_state_shape result).choose_spec.2.2.2

end Solcore.Syntax.Parser
