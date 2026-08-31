import Solcore.Syntax.DeriveValidity
import Solcore.Syntax.Parser.Derive

/-! Source-provenance laws for canonical derive-attribute parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem validPath_validFor :
    DeriveAttributeInternals.valid.ValidFor DeriveAttribute.ValidFor := by
  intro input inputValid
  unfold DeriveAttributeInternals.valid
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp only [bind, hashResult, Reply.ValidFor]
  | reject failure rejected =>
      have valid := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at valid
      simp only [bind, hashResult, Reply.ValidFor]
      exact valid
  | ok hash afterHash =>
      have hashValid := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at hashValid
      have hashShape := symbol_ok_state_shape .hash .topItem hashResult
      simp only [bind, hashResult]
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          simp only
          have valid := symbol_validFor .leftBracket .topItem afterHash
            hashValid.2.1
          rw [openingResult] at valid
          exact valid.of_file_eq hashValid.2.2
      | ok opening afterOpening =>
          simp only
          have openingValid := symbol_validFor .leftBracket .topItem afterHash
            hashValid.2.1
          rw [openingResult] at openingValid
          have openingShape := symbol_ok_state_shape .leftBracket .topItem
            openingResult
          cases deriveResult : contextual .derive .topItem afterOpening with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              simp only
              have valid := contextual_validFor .derive .topItem afterOpening
                openingValid.2.1
              rw [deriveResult] at valid
              exact valid.of_file_eq
                (openingValid.2.2.trans hashValid.2.2)
          | ok deriveKeyword afterDerive =>
              simp only
              have deriveValid := contextual_validFor .derive .topItem
                afterOpening openingValid.2.1
              rw [deriveResult] at deriveValid
              have deriveShape := acceptToken_ok_state_shape
                (.contextual .derive) .topItem (·.isContextual .derive)
                deriveResult
              cases targetsResult : delimitedNoTrailing .leftParen .rightParen
                  true deriveTarget .topItem .topLevel afterDerive with
              | invariant error => simp only [Reply.ValidFor]
              | reject failure rejected =>
                  simp only
                  have valid := delimitedNoTrailing_validFor
                    QualifiedName.ValidFor .leftParen .rightParen true
                    deriveTarget .topItem .topLevel deriveTarget_validFor
                    deriveTarget_preservesTokensOnSuccess afterDerive
                    deriveValid.2.1
                  rw [targetsResult] at valid
                  exact valid.of_file_eq (deriveValid.2.2.trans
                    (openingValid.2.2.trans hashValid.2.2))
              | ok targets afterTargets =>
                  simp only
                  have targetsValid := delimitedNoTrailing_validFor
                    QualifiedName.ValidFor .leftParen .rightParen true
                    deriveTarget .topItem .topLevel deriveTarget_validFor
                    deriveTarget_preservesTokensOnSuccess afterDerive
                    deriveValid.2.1
                  rw [targetsResult] at targetsValid
                  have targetsTokens :=
                    delimitedNoTrailing_preservesTokensOnSuccess
                      .leftParen .rightParen true deriveTarget .topItem
                      .topLevel deriveTarget_preservesTokensOnSuccess
                      afterDerive targets afterTargets targetsResult
                  have targetsCursor :=
                    delimitedNoTrailing_cursorMonotoneOnSuccess
                      .leftParen .rightParen true deriveTarget .topItem
                      .topLevel afterDerive targets afterTargets targetsResult
                  cases closingResult : symbol .rightBracket .topItem
                      afterTargets with
                  | invariant error => simp only [Reply.ValidFor]
                  | reject failure rejected =>
                      simp only
                      have valid := symbol_validFor .rightBracket .topItem
                        afterTargets targetsValid.2.1
                      rw [closingResult] at valid
                      exact valid.of_file_eq (targetsValid.2.2.trans
                        (deriveValid.2.2.trans
                          (openingValid.2.2.trans hashValid.2.2)))
                  | ok closing afterClosing =>
                      simp only
                      have closingValid := symbol_validFor .rightBracket
                        .topItem afterTargets targetsValid.2.1
                      rw [closingResult] at closingValid
                      have closingShape := symbol_ok_state_shape .rightBracket
                        .topItem closingResult
                      have hashFound :=
                        State.getElem?_eq_some_of_peek?_eq_some hashShape.1
                      have closingFound :=
                        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
                      have closingFoundInput :
                          input.tokens[afterTargets.cursor]? = some closing := by
                        simpa [targetsTokens, deriveShape.2, openingShape.2,
                          hashShape.2] using closingFound
                      have hashBeforeClosing :
                          hash.span.endByte ≤ closing.span.startByte := by
                        apply inputValid.token_end_le_token_start_of_getElem?_lt
                          hashFound closingFoundInput
                        have hashProgress : input.cursor < afterHash.cursor := by
                          rw [hashShape.2]
                          simp
                        have openingProgress :
                            afterHash.cursor < afterOpening.cursor := by
                          rw [openingShape.2]
                          simp
                        have deriveProgress :
                            afterOpening.cursor < afterDerive.cursor := by
                          rw [deriveShape.2]
                          simp
                        exact Nat.lt_of_lt_of_le
                          (Nat.lt_trans hashProgress
                            (Nat.lt_trans openingProgress deriveProgress))
                          targetsCursor
                      have hashSpanValid : hash.span.ValidFor input.file := by
                        simpa only [Located.ValidFor] using hashValid.1
                      have closingSpanValid :
                          closing.span.ValidFor input.file := by
                        simpa only [Located.ValidFor, closingValid.2.2,
                          targetsValid.2.2, deriveValid.2.2, openingValid.2.2,
                          hashValid.2.2] using closingValid.1
                      have spanValid := SourceSpan.cover_validFor hashSpanValid
                        closingSpanValid (Nat.le_trans hashSpanValid.2.1
                          (Nat.le_trans hashBeforeClosing
                            closingSpanValid.2.1))
                      have valueValid : DeriveAttribute.ValidFor input.file {
                          span := SourceSpan.cover hash.span closing.span
                          value := { targets }
                        } := ⟨spanValid, by
                          simpa [targetsValid.2.2, deriveValid.2.2,
                            openingValid.2.2, hashValid.2.2]
                            using targetsValid.1⟩
                      have spanValidAfter :
                          (SourceSpan.cover hash.span closing.span).ValidFor
                            afterClosing.file := by
                        simpa [closingValid.2.2, targetsValid.2.2,
                          deriveValid.2.2, openingValid.2.2, hashValid.2.2]
                          using spanValid
                      split
                      · exact ⟨valueValid,
                          closingValid.2.1.emit_validFor _ spanValidAfter,
                          closingValid.2.2.trans (targetsValid.2.2.trans
                            (deriveValid.2.2.trans
                              (openingValid.2.2.trans hashValid.2.2)))⟩
                      · exact ⟨valueValid, closingValid.2.1,
                          closingValid.2.2.trans (targetsValid.2.2.trans
                            (deriveValid.2.2.trans
                              (openingValid.2.2.trans hashValid.2.2)))⟩

private theorem finishRecovered_validFor (hash last : SourceSpan)
    (constraint : ParseConstraint) (state : State)
    (stateValid : state.ValidFor) (hashValid : hash.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : hash.startByte ≤ last.endByte) :
    (DeriveAttributeInternals.finishRecovered hash last constraint state).ValidFor
      state DeriveAttribute.ValidFor := by
  have spanValid := SourceSpan.cover_validFor hashValid lastValid ordered
  unfold DeriveAttributeInternals.finishRecovered Reply.ValidFor
    DeriveAttribute.ValidFor
  exact ⟨⟨spanValid, spanValid, by simp⟩,
    stateValid.emit_validFor _ spanValid, rfl⟩

private theorem recoverTail_validFor (hash : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → hash.ValidFor state.file → last.ValidFor state.file →
      hash.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (DeriveAttributeInternals.recoverTail hash last fuel state).ValidFor state
        DeriveAttribute.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid hashValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold DeriveAttributeInternals.recoverTail
      split
      · cases closingResult : symbol .rightBracket .topItem state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have valid := symbol_validFor .rightBracket .topItem state stateValid
            rw [closingResult] at valid
            simpa only [Reply.ValidFor] using valid
        | ok closing next =>
            have closingValid := symbol_validFor .rightBracket .topItem state
              stateValid
            rw [closingResult] at closingValid
            have closingShape := symbol_ok_state_shape .rightBracket .topItem
              closingResult
            have closingFound := State.getElem?_eq_some_of_peek?_eq_some
              closingShape.1
            have lastBeforeClosing :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                closingFound lastBefore
            have closingSpanValid : closing.span.ValidFor state.file := by
              simpa only [Located.ValidFor] using closingValid.1
            have coverOrdered : hash.startByte ≤ closing.span.endByte :=
              Nat.le_trans ordered (Nat.le_trans (by simpa [lastSpan] using
                lastBeforeClosing) closingSpanValid.2.1)
            exact (finishRecovered_validFor hash closing.span
              .malformedDeriveAttribute next closingValid.2.1
              (by simpa [closingValid.2.2] using hashValid)
              (by simpa [closingValid.2.2] using closingSpanValid)
              coverOrdered).of_file_eq closingValid.2.2
      · split
        · exact finishRecovered_validFor hash last .unclosedDeriveAttribute
            state stateValid hashValid lastValid ordered
        · cases advanced : state.advance? with
          | some pair =>
              rcases pair with ⟨token, next⟩
              have nextValid := stateValid.advance?_validFor advanced
              unfold State.advance? at advanced
              cases found : state.peek? with
              | none => simp [found] at advanced
              | some current =>
                  simp only [found, Option.map_some] at advanced
                  cases advanced
                  have tokenValid := stateValid.peek?_span_validFor found
                  have currentFound :=
                    State.getElem?_eq_some_of_peek?_eq_some found
                  have lastBeforeCurrent :=
                    stateValid.token_end_le_token_start_of_getElem?_lt
                      lastFound currentFound lastBefore
                  apply inductionHypothesis token.span
                    { state with cursor := state.cursor + 1 } state.cursor token
                    nextValid (by simpa using hashValid) (by simpa using tokenValid)
                  · exact Nat.le_trans ordered (Nat.le_trans
                      (by simpa [lastSpan] using lastBeforeCurrent)
                      tokenValid.2.1)
                  · exact currentFound
                  · rfl
                  · simp
          | none =>
              exact finishRecovered_validFor hash last .unclosedDeriveAttribute
                state stateValid hashValid lastValid ordered

private theorem recoveredPath_validFor :
    DeriveAttributeInternals.recovered.ValidFor DeriveAttribute.ValidFor := by
  intro input inputValid
  unfold DeriveAttributeInternals.recovered
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have valid := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at valid
      simpa only [Reply.ValidFor] using valid
  | ok hash afterHash =>
      have hashValid := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at hashValid
      have hashShape := symbol_ok_state_shape .hash .topItem hashResult
      simp only
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have valid := symbol_validFor .leftBracket .topItem afterHash
            hashValid.2.1
          rw [openingResult] at valid
          exact valid.of_file_eq hashValid.2.2
      | ok opening afterOpening =>
          have openingValid := symbol_validFor .leftBracket .topItem afterHash
            hashValid.2.1
          rw [openingResult] at openingValid
          have openingShape := symbol_ok_state_shape .leftBracket .topItem
            openingResult
          have hashFound := State.getElem?_eq_some_of_peek?_eq_some hashShape.1
          have openingFound := State.getElem?_eq_some_of_peek?_eq_some
            openingShape.1
          have hashBeforeOpening :=
            inputValid.token_end_le_token_start_of_getElem?_lt hashFound
              (by simpa [hashShape.2] using openingFound) (by simp)
          have hashSpanValid : hash.span.ValidFor afterOpening.file := by
            simpa only [Located.ValidFor, openingValid.2.2, hashValid.2.2]
              using hashValid.1
          have openingSpanValid : opening.span.ValidFor afterOpening.file := by
            simpa only [Located.ValidFor, openingValid.2.2] using openingValid.1
          exact (recoverTail_validFor hash.span
            (afterOpening.remainingCount + 1) opening.span afterOpening
            afterHash.cursor opening openingValid.2.1 hashSpanValid
            openingSpanValid (Nat.le_trans hashSpanValid.2.1
              (Nat.le_trans hashBeforeOpening openingSpanValid.2.1))
            (by simpa [openingShape.2] using openingFound) rfl (by
              rw [openingShape.2]
              simp)).of_file_eq (openingValid.2.2.trans hashValid.2.2)

/-- Derive attributes preserve every retained source range. -/
theorem deriveAttribute_validFor :
    deriveAttribute.ValidFor DeriveAttribute.ValidFor :=
  Parser.orElse_validFor validPath_validFor recoveredPath_validFor

end Solcore.Syntax.Parser
