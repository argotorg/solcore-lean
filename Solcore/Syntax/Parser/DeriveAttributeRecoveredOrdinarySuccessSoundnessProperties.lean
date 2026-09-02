import Solcore.Syntax.Parser.DeriveAttributeRecoveryBoundaryProperties

/-! Exact ordinary-success reflection for derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.DeriveAttributeInternals

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

/-- Every successful malformed-tail scan follows the exact priority-ordered
declarative recovery relation, at any fuel. -/
theorem recoverTail_success_ordinaryOutcome_sound (hash : SourceSpan) :
    ∀ fuel last input value output,
      recoverTail hash last fuel input = .ok value output →
      DeclarativeGrammar.DeriveAttributeRecoveryTailParses hash last
        input.declarativeRemainder value output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input value output result
      simp [recoverTail] at result
  | succ fuel inductionHypothesis =>
      intro last input value output result
      unfold recoverTail at result
      cases closingPresent : isSymbol input .rightBracket with
      | true =>
          simp only [closingPresent, if_true] at result
          cases closingResult : symbol .rightBracket .topItem input with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing afterClosing =>
              simp only [closingResult] at result
              unfold finishRecovered at result
              cases result
              simpa [State.emit, State.declarativeRemainder,
                DeclarativeGrammar.recoveredDeriveAttributeValue] using
                (DeclarativeGrammar.DeriveAttributeRecoveryTailParses.malformed
                  (hash := hash) (last := last) closing.span
                  (symbol_success_exactTokenParses .rightBracket .topItem
                    closingResult))
      | false =>
          have closingAbsent :=
            symbolAbsentAt_of_isSymbol_eq_false .rightBracket closingPresent
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases unclosedGuard :
              (input.atEnd || atDeriveDeclarationBoundary input) with
          | true =>
              simp only [unclosedGuard, if_true] at result
              unfold finishRecovered at result
              cases result
              simpa [State.emit, State.declarativeRemainder,
                DeclarativeGrammar.recoveredDeriveAttributeValue] using
                (DeclarativeGrammar.DeriveAttributeRecoveryTailParses.unclosed
                  (hash := hash) (last := last) closingAbsent
                  (recoveryStops_of_unclosedGuard_eq_true input
                    unclosedGuard))
          | false =>
              simp only [unclosedGuard, Bool.false_eq_true, if_false] at result
              cases advanced : input.advance? with
              | none =>
                  simp only [advanced] at result
                  unfold finishRecovered at result
                  cases result
                  simpa [State.emit, State.declarativeRemainder,
                    DeclarativeGrammar.recoveredDeriveAttributeValue] using
                    (DeclarativeGrammar.DeriveAttributeRecoveryTailParses.unclosed
                      (hash := hash) (last := last) closingAbsent
                      (recoveryStops_of_advance?_eq_none input unclosedGuard
                        advanced))
              | some pair =>
                  rcases pair with ⟨token, next⟩
                  simp only [advanced] at result
                  rcases advance?_state_shape advanced with ⟨found, nextEq⟩
                  have tail := inductionHypothesis token.span next value output
                    result
                  rw [nextEq] at tail
                  exact .next closingAbsent
                    (no_recoveryStops_of_nonBoundary_token unclosedGuard found)
                    (tokenAt_of_peek?_eq_some found) tail

/-- Production fuel specializes successful malformed-tail reflection. -/
theorem recoverTail_production_success_ordinaryOutcome_sound
    (hash last : SourceSpan) {input output : State}
    {value : DeriveAttribute}
    (result : recoverTail hash last (input.remainingCount + 1) input =
      .ok value output) :
    DeclarativeGrammar.DeriveAttributeRecoveryTailParses hash last
      input.declarativeRemainder value output.declarativeRemainder :=
  recoverTail_success_ordinaryOutcome_sound hash
    (input.remainingCount + 1) last input value output result

/-- Every successful recovered derive path consumes the exact `#[` prefix and
then follows the exact malformed-tail recovery relation. -/
theorem recovered_success_ordinaryOutcome_sound
    {input output : State} {value : DeriveAttribute}
    (result : recovered input = .ok value output) :
    DeclarativeGrammar.DeriveAttributeRecoveredParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold recovered at result
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
          exact .recovered hash.span opening.span
            (symbol_success_exactTokenParses .hash .topItem hashResult)
            (symbol_success_exactTokenParses .leftBracket .topItem
              openingResult)
            (recoverTail_production_success_ordinaryOutcome_sound hash.span
              opening.span result)

end Solcore.Syntax.Parser.DeriveAttributeInternals
