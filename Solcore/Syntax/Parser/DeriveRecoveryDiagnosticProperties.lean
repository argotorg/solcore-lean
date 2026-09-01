import Solcore.Syntax.Parser.Derive

/-! Diagnostics produced by canonical derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful recovered derive tail retains a recovery diagnostic. -/
theorem deriveRecoverTail_success_hasDiagnostic (hash : SourceSpan) :
    ∀ fuel last input value next,
      DeriveAttributeInternals.recoverTail hash last fuel input =
          .ok value next →
        next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input value next result
      simp [DeriveAttributeInternals.recoverTail] at result
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
            simp [State.emit]
      · split at result
        · unfold DeriveAttributeInternals.finishRecovered at result
          cases result
          simp [State.emit]
        · cases advanced : input.advance? with
          | some pair =>
              rcases pair with ⟨token, afterToken⟩
              simp only [advanced] at result
              exact inductionHypothesis token.span afterToken value next result
          | none =>
              simp only [advanced] at result
              unfold DeriveAttributeInternals.finishRecovered at result
              cases result
              simp [State.emit]

/-- Every success of the recovered derive-attribute path has a diagnostic. -/
theorem deriveRecovered_success_hasDiagnostic {input next : State}
    {value : DeriveAttribute}
    (result : DeriveAttributeInternals.recovered input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
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
          exact deriveRecoverTail_success_hasDiagnostic hash.span
            (afterOpening.remainingCount + 1) opening.span afterOpening value
            next result

end Solcore.Syntax.Parser
