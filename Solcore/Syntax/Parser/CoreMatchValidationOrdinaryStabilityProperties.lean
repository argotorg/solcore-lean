import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Statement.Match

/-! Ordinary stability of diagnostic-only Core match validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- One arity check always succeeds without changing the declarative
remainder. -/
theorem validateMatchCaseArity_succeeds_stable
    (scrutineeCount : Nat) (arm : MatchCase) (input : State) :
    ∃ output,
      validateMatchCaseArity scrutineeCount arm input = .ok () output ∧
        output.declarativeRemainder = input.declarativeRemainder := by
  unfold validateMatchCaseArity
  split
  · exact ⟨input, rfl, rfl⟩
  · exact ⟨input.emit _, rfl, rfl⟩

/-- The complete arity pass always succeeds and changes diagnostics only. -/
theorem validateMatchArities_succeeds_stable (scrutineeCount : Nat) :
    ∀ cases input, ∃ output,
      validateMatchArities scrutineeCount cases input = .ok () output ∧
        output.declarativeRemainder = input.declarativeRemainder := by
  intro cases
  induction cases with
  | nil =>
      intro input
      exact ⟨input, rfl, rfl⟩
  | cons arm rest inductionHypothesis =>
      intro input
      rcases validateMatchCaseArity_succeeds_stable scrutineeCount arm input
          with ⟨afterArm, armResult, afterArmStable⟩
      rcases inductionHypothesis afterArm with
        ⟨output, restResult, outputStable⟩
      refine ⟨output, ?_, outputStable.trans afterArmStable⟩
      simp only [validateMatchArities, bind, armResult, restResult]

end Solcore.Syntax.Parser.MatchInternals
