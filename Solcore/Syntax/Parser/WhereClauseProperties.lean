import Solcore.Syntax.Parser.PredicateSequenceProperties

/-! Public contracts for optional canonical `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional `where` parsing retains its marker and every predicate range. -/
theorem whereClause_validFor :
    whereClause.ValidFor (Option.ValidFor WhereClause.ValidFor) := by
  have weak : whereClause.ValidFor (fun _ _ => True) := by
    unfold whereClause
    apply Parser.bind_validFor getState_validFor
    intro observed
    by_cases present : isContextual observed .where
    · simp only [present, if_true]
      apply Parser.bind_validFor (contextual_validFor .where .typeExpr)
      intro marker
      apply Parser.bind_validFor PredicateInternals.predicateSequence_validFor
      intro predicates
      exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
    · simp only [present]
      exact Parser.pure_validFor none (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : whereClause input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold whereClause getState at stages
      simp only [bind] at stages
      by_cases present : isContextual input .where
      · simp only [present, if_true] at stages
        rcases predicateBind_ok_components stages with
          ⟨marker, afterMarker, markerResult, rest⟩
        rcases predicateBind_ok_components rest with
          ⟨predicates, afterPredicates, predicatesResult, finished⟩
        have markerValid := contextual_validFor .where .typeExpr input
          inputValid
        rw [markerResult] at markerValid
        have predicatesValid := PredicateInternals.predicateSequence_validFor
          afterMarker markerValid.2.1
        rw [predicatesResult] at predicatesValid
        have markerSpanValid : marker.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using markerValid.1
        have predicatesValidInput : NonemptyDelimitedList.ValidFor
            Predicate.ValidFor input.file predicates := by
          simpa [markerValid.2.2] using predicatesValid.1
        have markerShape := acceptToken_ok_state_shape
          (.contextual .where) .typeExpr (·.isContextual .where) markerResult
        have markerAdvanced : input.advance? = some (marker, afterMarker) := by
          unfold State.advance?
          rw [markerShape.1, markerShape.2]
          rfl
        rcases PredicateInternals.predicateSequence_startsAtCurrentTokenOnSuccess
            afterMarker predicates afterPredicates predicatesResult with
          ⟨first, firstFound, predicatesStart⟩
        have markerBeforePredicates :=
          inputValid.consumed_end_le_peek_start_after_advance markerAdvanced
            firstFound
        have ordered : marker.span.startByte ≤ predicates.span.endByte :=
          Nat.le_trans markerSpanValid.2.1
            (Nat.le_trans markerBeforePredicates (by
              rw [predicatesStart]
              exact predicatesValidInput.1.2.1))
        have outerValid := SourceSpan.cover_validFor markerSpanValid
          predicatesValidInput.1 ordered
        cases finished
        exact ⟨by
            simpa only [Option.ValidFor] using
              (show WhereClause.ValidFor input.file {
                span := SourceSpan.cover marker.span predicates.span
                predicates := predicates.elements
              } from ⟨outerValid, by
                simpa [NonemptyList.ValidFor] using predicatesValidInput.2⟩),
          weakResult.2.1, weakResult.2.2⟩
      · simp only [present, Bool.false_eq_true, if_false] at stages
        cases stages
        exact ⟨trivial, inputValid, rfl⟩

/-- Optional `where` parsing preserves every ordinary token window. -/
theorem whereClause_preservesTokenWindow :
    Parser.PreservesTokenWindow whereClause := by
  unfold whereClause
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindow
  intro observed
  by_cases present : isContextual observed .where
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (contextual_preservesTokenWindow .where .typeExpr)
    intro marker
    apply Parser.bind_preservesTokenWindow
      PredicateInternals.predicateSequence_preservesTokenWindow
    intro predicates
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem whereClause_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess whereClause :=
  whereClause_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional `where` parsing never rewinds the cursor. -/
theorem whereClause_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess whereClause := by
  unfold whereClause
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isContextual observed .where
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (contextual_cursorMonotoneOnSuccess .where .typeExpr)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      PredicateInternals.predicateSequence_cursorMonotoneOnSuccess
    intro predicates
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present `where` clause starts at its contextual marker token. -/
theorem whereClause_some_startsAtCurrentTokenOnSuccess
    {input final : State} {clause : WhereClause}
    (parsed : whereClause input = .ok (some clause) final) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = clause.span.startByte := by
  unfold whereClause getState at parsed
  simp only [bind] at parsed
  by_cases present : isContextual input .where
  · simp only [present, if_true] at parsed
    rcases predicateBind_ok_components parsed with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases predicateBind_ok_components rest with
      ⟨predicates, afterPredicates, predicatesResult, finished⟩
    rcases contextual_startsAtCurrentTokenOnSuccess .where .typeExpr input
        marker afterMarker markerResult with ⟨token, found, start⟩
    cases finished
    exact ⟨token, found, by simpa [SourceSpan.cover] using start⟩
  · simp only [present, Bool.false_eq_true, if_false] at parsed
    cases parsed

end Solcore.Syntax.Parser
