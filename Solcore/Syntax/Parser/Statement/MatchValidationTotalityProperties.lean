import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.Statement.MatchProperties

/-! Totality for the diagnostic-only Core-match arity validation pass. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- One arity check either returns directly or emits one diagnostic. -/
theorem validateMatchCaseArity_ordinary
    (scrutineeCount : Nat) (retainedCase : MatchCase) :
    Parser.Ordinary
      (validateMatchCaseArity scrutineeCount retainedCase) := by
  intro input
  unfold validateMatchCaseArity
  split
  · exact Or.inl ⟨(), input, rfl⟩
  · exact Or.inl ⟨(), input.emit _, rfl⟩

/-- The finite arity-validation pass has no internal failure outcome. -/
theorem validateMatchArities_ordinary (scrutineeCount : Nat) :
    ∀ cases, Parser.Ordinary (validateMatchArities scrutineeCount cases)
  | [] => fun input => Or.inl ⟨(), input, rfl⟩
  | retainedCase :: rest => by
      intro input
      rcases validateMatchCaseArity_ordinary scrutineeCount retainedCase
          input with
        ⟨checked, afterCheck, checkResult⟩ |
        ⟨failure, rejected, checkResult⟩
      · rcases validateMatchArities_ordinary scrutineeCount rest afterCheck with
          ⟨value, final, restResult⟩ |
          ⟨failure, rejected, restResult⟩
        · exact Or.inl ⟨value, final, by
            simp only [validateMatchArities, bind, checkResult, restResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [validateMatchArities, bind, checkResult, restResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [validateMatchArities, bind, checkResult]⟩

theorem validateMatchArities_invariantFreeOnValid
    (scrutineeCount : Nat) (cases : List MatchCase) :
    Parser.InvariantFreeOnValid
      (validateMatchArities scrutineeCount cases) :=
  (validateMatchArities_ordinary scrutineeCount cases).invariantFreeOnValid

theorem validateMatchArities_ne_invariant
    (scrutineeCount : Nat) (cases : List MatchCase)
    (input : State) (error : ParserInvariantError) :
    validateMatchArities scrutineeCount cases input ≠ .invariant error :=
  (validateMatchArities_ordinary scrutineeCount cases).ne_invariant input error

end Solcore.Syntax.Parser.MatchInternals
