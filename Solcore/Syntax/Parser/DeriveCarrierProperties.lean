import Solcore.Syntax.Parser.DeriveValidityProperties

/-! Token-carrier and cursor laws for canonical derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem validPath_ok_state_shape {input next : State}
    {value : DeriveAttribute}
    (result : DeriveAttributeInternals.valid input = .ok value next) :
    ∃ hash, input.peek? = some hash ∧
      hash.span.startByte = value.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold DeriveAttributeInternals.valid at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error =>
      simp only [bind, hashResult] at result
      contradiction
  | reject failure rejected =>
      simp only [bind, hashResult] at result
      contradiction
  | ok hash afterHash =>
      simp only [bind, hashResult] at result
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp [openingResult] at result
      | reject failure rejected => simp [openingResult] at result
      | ok opening afterOpening =>
          simp only [openingResult] at result
          cases deriveResult : contextual .derive .topItem afterOpening with
          | invariant error => simp [deriveResult] at result
          | reject failure rejected => simp [deriveResult] at result
          | ok deriveKeyword afterDerive =>
              simp only [deriveResult] at result
              cases targetsResult : delimitedNoTrailing .leftParen .rightParen
                  true deriveTarget .topItem .topLevel afterDerive with
              | invariant error => simp [targetsResult] at result
              | reject failure rejected => simp [targetsResult] at result
              | ok targets afterTargets =>
                  simp only [targetsResult] at result
                  cases closingResult : symbol .rightBracket .topItem
                      afterTargets with
                  | invariant error => simp [closingResult] at result
                  | reject failure rejected => simp [closingResult] at result
                  | ok closing afterClosing =>
                      simp only [closingResult] at result
                      have hashShape := symbol_ok_state_shape .hash .topItem
                        hashResult
                      have openingShape := symbol_ok_state_shape .leftBracket
                        .topItem openingResult
                      have deriveShape := acceptToken_ok_state_shape
                        (.contextual .derive) .topItem
                        (·.isContextual .derive) deriveResult
                      have targetsTokens :=
                        delimitedNoTrailing_preservesTokensOnSuccess
                          .leftParen .rightParen true deriveTarget .topItem
                          .topLevel deriveTarget_preservesTokensOnSuccess
                          afterDerive targets afterTargets targetsResult
                      have targetsCursor :=
                        delimitedNoTrailing_cursorMonotoneOnSuccess
                          .leftParen .rightParen true deriveTarget .topItem
                          .topLevel afterDerive targets afterTargets
                          targetsResult
                      have closingShape := symbol_ok_state_shape .rightBracket
                        .topItem closingResult
                      split at result
                      · simp only [emitDiagnostic, modifyState] at result
                        cases result
                        refine ⟨hash, hashShape.1, rfl, ?_, ?_⟩
                        · simp [State.emit, closingShape.2, targetsTokens,
                            deriveShape.2, openingShape.2, hashShape.2]
                        · simp [State.emit, closingShape.2, deriveShape.2,
                            openingShape.2, hashShape.2] at targetsCursor ⊢
                          omega
                      · cases result
                        refine ⟨hash, hashShape.1, rfl, ?_, ?_⟩
                        · simpa [closingShape.2, deriveShape.2, openingShape.2,
                            hashShape.2] using targetsTokens
                        · simp [closingShape.2, deriveShape.2, openingShape.2,
                            hashShape.2] at targetsCursor ⊢
                          omega

private theorem recoverTail_ok_state_shape (hash : SourceSpan) :
    ∀ fuel last input value next,
      DeriveAttributeInternals.recoverTail hash last fuel input =
        .ok value next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        value.span.startByte = hash.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last input value next result
      unfold DeriveAttributeInternals.recoverTail at result
      split at result
      · cases closingResult : symbol .rightBracket .topItem input with
        | invariant error => simp [closingResult] at result
        | reject failure rejected => simp [closingResult] at result
        | ok closing afterClosing =>
            simp only [closingResult] at result
            unfold DeriveAttributeInternals.finishRecovered at result
            cases result
            rw [(symbol_ok_state_shape .rightBracket .topItem closingResult).2]
            exact ⟨rfl, Nat.le_add_right _ 1, rfl⟩
      · split at result
        · unfold DeriveAttributeInternals.finishRecovered at result
          cases result
          exact ⟨rfl, Nat.le_refl _, rfl⟩
        · cases advanced : input.advance? with
          | some pair =>
              rcases pair with ⟨token, afterToken⟩
              simp only [advanced] at result
              have recursive := inductionHypothesis token.span afterToken
                value next result
              unfold State.advance? at advanced
              cases found : input.peek? with
              | none => simp [found] at advanced
              | some current =>
                  simp only [found, Option.map_some] at advanced
                  cases advanced
                  exact ⟨recursive.1, Nat.le_trans
                    (Nat.le_add_right input.cursor 1) recursive.2.1,
                    recursive.2.2⟩
          | none =>
              simp only [advanced] at result
              unfold DeriveAttributeInternals.finishRecovered at result
              cases result
              exact ⟨rfl, Nat.le_refl _, rfl⟩

private theorem recoveredPath_ok_state_shape {input next : State}
    {value : DeriveAttribute}
    (result : DeriveAttributeInternals.recovered input = .ok value next) :
    ∃ hash, input.peek? = some hash ∧
      hash.span.startByte = value.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold DeriveAttributeInternals.recovered at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp [hashResult] at result
  | reject failure rejected => simp [hashResult] at result
  | ok hash afterHash =>
      simp only [hashResult] at result
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp [openingResult] at result
      | reject failure rejected => simp [openingResult] at result
      | ok opening afterOpening =>
          simp only [openingResult] at result
          have tailShape := recoverTail_ok_state_shape hash.span
            (afterOpening.remainingCount + 1) opening.span afterOpening
            value next result
          have hashShape := symbol_ok_state_shape .hash .topItem hashResult
          have openingShape := symbol_ok_state_shape .leftBracket .topItem
            openingResult
          refine ⟨hash, hashShape.1, tailShape.2.2.symm, ?_, ?_⟩
          · simpa [openingShape.2, hashShape.2] using tailShape.1
          · exact Nat.lt_of_lt_of_le (by
              simp [openingShape.2, hashShape.2]
              omega) tailShape.2.1

private theorem deriveAttribute_ok_state_shape {input next : State}
    {value : DeriveAttribute}
    (result : deriveAttribute input = .ok value next) :
    ∃ hash, input.peek? = some hash ∧
      hash.span.startByte = value.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold deriveAttribute orElse at result
  cases validResult : DeriveAttributeInternals.valid input with
  | ok value afterValid =>
      simp only [validResult] at result
      cases result
      exact validPath_ok_state_shape validResult
  | reject failure rejected =>
      simp only [validResult] at result
      exact recoveredPath_ok_state_shape result
  | invariant error => simp [validResult] at result

/-- Derive-attribute success preserves the immutable token carrier. -/
theorem deriveAttribute_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess deriveAttribute := by
  intro input value next result
  exact (deriveAttribute_ok_state_shape result).choose_spec.2.2.1

/-- A derive attribute starts at its retained hash token. -/
theorem deriveAttribute_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess deriveAttribute (·.span) := by
  intro input value next result
  rcases deriveAttribute_ok_state_shape result with
    ⟨hash, found, start, _tokens, _cursor⟩
  exact ⟨hash, found, start⟩

/-- Every successful derive attribute consumes at least its `#[` prefix. -/
theorem deriveAttribute_cursor_lt_onSuccess {input next : State}
    {value : DeriveAttribute}
    (result : deriveAttribute input = .ok value next) :
    input.cursor < next.cursor :=
  (deriveAttribute_ok_state_shape result).choose_spec.2.2.2

/-- Derive-attribute success never moves the token cursor backwards. -/
theorem deriveAttribute_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess deriveAttribute := by
  intro input value next result
  exact Nat.le_of_lt (deriveAttribute_cursor_lt_onSuccess result)

end Solcore.Syntax.Parser
