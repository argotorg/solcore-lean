import Solcore.Syntax.Parser.TypeAlias

/-! Diagnostic commitments of transparent type-alias value recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TypeAliasInternals

/-- Every successful auxiliary alias recovery commits a recovery diagnostic. -/
theorem recoverTypeAliasValueAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : TypeExpr},
      recoverTypeAliasValueAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverTypeAliasValueAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverTypeAliasValueAux at recovered
      split at recovered
      · unfold finishRecoveredType at recovered
        cases recovered
        simp [State.emit]
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            unfold finishRecoveredType at recovered
            cases recovered
            simp [State.emit]
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- Every successful complete alias recovery commits a recovery diagnostic. -/
theorem recoverTypeAliasValue_diagnostics_ne_nil_onSuccess
    {input next : State} {value : TypeExpr}
    (recovered : recoverTypeAliasValue input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverTypeAliasValue at recovered
  split at recovered
  · unfold rejectAt at recovered
    contradiction
  · cases advanced : input.advance? with
    | none =>
        simp [advanced, rejectAt] at recovered
    | some pair =>
        rcases pair with ⟨token, afterToken⟩
        simp only [advanced] at recovered
        exact recoverTypeAliasValueAux_diagnostics_ne_nil_onSuccess
          token.span token.span (afterToken.remainingCount + 1) recovered

end Solcore.Syntax.Parser.TypeAliasInternals
