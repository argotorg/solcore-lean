import Solcore.Syntax.Parser.Contract

/-! Diagnostic commitments of contract-member recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Finishing a recovered contract member always emits its recovery diagnostic. -/
theorem finishRecoveredMember_success_hasDiagnostic
    (first last : SourceSpan) {input next : State} {member : ContractMember}
    (result : finishRecoveredMember first last input = .ok member next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecoveredMember at result
  cases result
  simp [State.emit]

/-- Every successful auxiliary contract-member recovery retains a diagnostic. -/
theorem recoverContractMemberAux_success_hasDiagnostic
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {member : ContractMember},
      recoverContractMemberAux first last fuel input = .ok member next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverContractMemberAux]
  | succ fuel inductionHypothesis =>
      intro input next member recovered
      unfold recoverContractMemberAux at recovered
      split at recovered
      · exact finishRecoveredMember_success_hasDiagnostic first last recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecoveredMember_success_hasDiagnostic first last recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- Every successful public contract-member recovery retains a diagnostic. -/
theorem recoverContractMember_success_hasDiagnostic
    {input next : State} {member : ContractMember}
    (recovered : recoverContractMember input = .ok member next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverContractMember at recovered
  cases advanced : input.advance? with
  | none =>
      simp [advanced, rejectAt] at recovered
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at recovered
      exact recoverContractMemberAux_success_hasDiagnostic token.span token.span
        (afterToken.remainingCount + 1) recovered

end Solcore.Syntax.Parser.ContractInternals
