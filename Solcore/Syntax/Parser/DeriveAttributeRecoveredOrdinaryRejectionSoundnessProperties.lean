import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Derive

/-! Exact ordinary-rejection reflection for derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.DeriveAttributeInternals

/-- The malformed-tail scan can succeed or expose an invariant, but cannot
return an ordinary rejection at any fuel. -/
private theorem recoverTail_ne_reject_recursive
    (hash : SourceSpan) :
    ∀ fuel last input failure rejected,
      recoverTail hash last fuel input ≠ .reject failure rejected := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input failure rejected
      simp [recoverTail]
  | succ fuel inductionHypothesis =>
      intro last input failure rejected
      unfold recoverTail
      split
      · have closingPresent : isSymbol input .rightBracket = true := by
          assumption
        cases closingResult : symbol .rightBracket .topItem input with
        | ok closing next =>
            simp [finishRecovered]
        | reject closingFailure closingRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .rightBracket .topItem
                closingPresent with ⟨closing, parsed⟩
            rw [parsed] at closingResult
            contradiction
        | invariant error =>
            simp
      · split
        · simp [finishRecovered]
        · cases advanced : input.advance? with
          | none => simp [finishRecovered]
          | some pair =>
              rcases pair with ⟨token, next⟩
              exact inductionHypothesis token.span next failure rejected

/-- Every recovery-path rejection is an exact missing hash or missing opening
bracket; the production malformed-tail scan contributes no rejection. -/
theorem recovered_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : recovered input = .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeRecoveredRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recovered at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error =>
      simp [hashResult] at result
  | reject hashFailure hashRejected =>
      have rejectedEq := symbol_reject_state_eq .hash .topItem hashResult
      subst hashRejected
      simp only [hashResult] at result
      cases result
      exact .hashMissing
        (symbol_reject_tokenKindAbsentAt .hash .topItem hashResult)
  | ok hash afterHash =>
      simp only [hashResult] at result
      have hashParsed := symbol_success_exactTokenParses .hash .topItem
        hashResult
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error =>
          simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have rejectedEq := symbol_reject_state_eq .leftBracket .topItem
            openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          exact .openingMissing hash.span hashParsed
            (symbol_reject_tokenKindAbsentAt .leftBracket .topItem
              openingResult)
      | ok opening afterOpening =>
          simp only [openingResult] at result
          exact False.elim
            (recoverTail_ne_reject_recursive hash.span
              (afterOpening.remainingCount + 1) opening.span afterOpening
              failure rejected result)

end Solcore.Syntax.Parser.DeriveAttributeInternals
