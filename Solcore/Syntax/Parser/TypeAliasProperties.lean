import Solcore.Syntax.Parser.TypeAlias
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.TypeDeclarationValidity

/-! Recovery and declaration contracts for transparent type aliases. -/
set_option autoImplicit false
namespace Solcore.Syntax.Parser
namespace TypeAliasInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩
/-- Finishing alias recovery retains one source-valid error range. -/
theorem finishRecoveredType_validFor (span : SourceSpan) (state : State)
    (stateValid : state.ValidFor) (spanValid : span.ValidFor state.file) :
    (finishRecoveredType span state).ValidFor state TypeExpr.ValidFor := by
  unfold finishRecoveredType Reply.ValidFor
  exact ⟨.error spanValid, stateValid.emit_validFor _ spanValid, rfl⟩
/-- Alias recovery preserves provenance while consuming malformed tokens. -/
theorem recoverTypeAliasValueAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverTypeAliasValueAux first last fuel state).ValidFor state
        TypeExpr.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverTypeAliasValueAux
      split
      · exact finishRecoveredType_validFor _ _ stateValid
          (SourceSpan.cover_validFor firstValid lastValid ordered)
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredType_validFor _ _ stateValid
              (SourceSpan.cover_validFor firstValid lastValid ordered)
        | some pair =>
            rcases pair with ⟨token, next⟩
            have nextValid := stateValid.advance?_validFor advanced
            have shape := advance?_state_shape advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt
                lastFound currentFound lastBefore
            have recursive := inductionHypothesis token.span next state.cursor
              token nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl (by
                simp [shape.2])
            exact recursive.of_file_eq (by simp [shape.2])
/-- The complete recovering RHS parser preserves recursive type provenance. -/
theorem recoverTypeAliasValue_validFor (state : State)
    (stateValid : state.ValidFor) :
    (recoverTypeAliasValue state).ValidFor state TypeExpr.ValidFor := by
  unfold recoverTypeAliasValue
  split
  · unfold rejectAt Reply.ValidFor
    exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
  · cases advanced : state.advance? with
    | none =>
        unfold rejectAt Reply.ValidFor
        exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
    | some pair =>
        rcases pair with ⟨token, next⟩
        have shape := advance?_state_shape advanced
        have nextValid := stateValid.advance?_validFor advanced
        have tokenValid := stateValid.peek?_span_validFor shape.1
        have tokenFound := State.getElem?_eq_some_of_peek?_eq_some shape.1
        exact (recoverTypeAliasValueAux_validFor token.span
          (next.remainingCount + 1) token.span next state.cursor token
          nextValid (by simpa [shape.2] using tokenValid)
          (by simpa [shape.2] using tokenValid) tokenValid.2.1
          (by simpa [shape.2] using tokenFound) rfl (by
            simp [shape.2])).of_file_eq (by simp [shape.2])
/-- Parsing or recovering an alias RHS retains source-valid type syntax. -/
theorem parseAliasValue_validFor :
    parseAliasValue.ValidFor TypeExpr.ValidFor := by
  intro input inputValid
  unfold parseAliasValue
  cases coreResult : typeExpr input with
  | ok value next =>
      have valid := typeExpr_validFor input inputValid
      rw [coreResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have coreValid := typeExpr_validFor input inputValid
      rw [coreResult] at coreValid
      have coreShape := typeExpr_preservesTokenWindow input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := coreValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, coreShape.2] using inputValid.cursor_le_endIndex
        endIndex_le_size := coreValid.2.1.endIndex_le_size
        endByte_le_source := coreValid.2.1.endByte_le_source
        endByte_boundary := coreValid.2.1.endByte_boundary
        diagnosticsRev := coreValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using coreValid.2.2
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          Reply.reject failure rewound
        else recoverTypeAliasValue (rewound.emit failure.toDiagnostic)).ValidFor
          input TypeExpr.ValidFor
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · have failureValid : failure.span.ValidFor rewound.file := by
          simpa [rewound, coreValid.2.2] using coreValid.1
        have emittedValid := rewoundValid.emit_validFor failure.toDiagnostic
          (failure.toDiagnostic_span_validFor failureValid)
        exact (recoverTypeAliasValue_validFor
          (rewound.emit failure.toDiagnostic) emittedValid).of_file_eq
            (by simpa [State.emit] using rewoundFile)
/-- Recovery preserves the complete immutable token window. -/
theorem recoverTypeAliasValueAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow
      (recoverTypeAliasValueAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverTypeAliasValueAux
      split
      · unfold finishRecoveredType Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecoveredType Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            exact (inductionHypothesis token.span next).trans (by
              simp [(advance?_state_shape advanced).2])
/-- The recovering RHS entry point preserves every ordinary token window. -/
theorem recoverTypeAliasValue_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverTypeAliasValue := by
  intro input
  unfold recoverTypeAliasValue
  split
  · exact rejectAt_preservesTokenWindow input _ _
  · cases advanced : input.advance? with
    | none => exact rejectAt_preservesTokenWindow input _ _
    | some pair =>
        rcases pair with ⟨token, next⟩
        exact (recoverTypeAliasValueAux_preservesTokenWindow token.span
          token.span (next.remainingCount + 1) next).trans (by
            simp [(advance?_state_shape advanced).2])
/-- Alias RHS parsing and recovery preserve every ordinary token window. -/
theorem parseAliasValue_preservesTokenWindow :
    Parser.PreservesTokenWindow parseAliasValue := by
  intro input
  unfold parseAliasValue
  have coreShape := typeExpr_preservesTokenWindow input
  cases coreResult : typeExpr input with
  | ok value next => rw [coreResult] at coreShape; exact coreShape
  | invariant error => trivial
  | reject failure failedState =>
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := by
        exact ⟨by simp [rewound, coreShape.1],
          by simp [rewound, coreShape.2]⟩
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          Reply.reject failure rewound
        else recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)).PreservesTokenWindow input
      split
      · exact rewoundShape
      · exact (recoverTypeAliasValue_preservesTokenWindow
          (rewound.emit failure.toDiagnostic)).trans (by
            simpa [State.emit] using rewoundShape)

/-- Successful alias RHS parsing retains the immutable token carrier. -/
theorem parseAliasValue_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess parseAliasValue :=
  parseAliasValue_preservesTokenWindow.preservesTokensOnSuccess

/-- Recovery never rewinds the cursor on success. -/
theorem recoverTypeAliasValueAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess
      (recoverTypeAliasValueAux first last fuel) := by
  intro input value next result
  induction fuel generalizing last input with
  | zero => contradiction
  | succ fuel inductionHypothesis =>
      unfold recoverTypeAliasValueAux at result
      split at result
      · unfold finishRecoveredType at result
        cases result
        exact Nat.le_refl _
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredType at result
            cases result
            exact Nat.le_refl _
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have advanceCursor : input.cursor ≤ afterToken.cursor := by
              rw [(advance?_state_shape advanced).2]
              exact Nat.le_add_right _ 1
            exact Nat.le_trans advanceCursor
              (inductionHypothesis token.span afterToken result)

/-- The recovering RHS entry point is cursor-monotone on success. -/
theorem recoverTypeAliasValue_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess recoverTypeAliasValue := by
  intro input value next result
  unfold recoverTypeAliasValue at result
  split at result
  · unfold rejectAt at result; contradiction
  · cases advanced : input.advance? with
    | none => simp [advanced, rejectAt] at result
    | some pair =>
        rcases pair with ⟨token, afterToken⟩
        simp only [advanced] at result
        exact Nat.le_trans (by
          rw [(advance?_state_shape advanced).2]
          exact Nat.le_add_right _ 1)
          (recoverTypeAliasValueAux_cursorMonotoneOnSuccess token.span
            token.span (afterToken.remainingCount + 1)
            afterToken value next result)

/-- Alias RHS parsing and recovery never rewind the parser cursor. -/
theorem parseAliasValue_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess parseAliasValue := by
  intro input value next result
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok parsed afterCore =>
      simp only [coreResult] at result
      have monotone := typeExpr_cursorMonotoneOnSuccess
        input parsed afterCore coreResult
      cases result
      exact monotone
  | invariant error => simp [coreResult] at result
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          Reply.reject failure rewound
        else recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · simpa [rewound, State.emit] using
          (recoverTypeAliasValue_cursorMonotoneOnSuccess
            (rewound.emit failure.toDiagnostic) value next result)

end TypeAliasInternals
end Solcore.Syntax.Parser
