import Solcore.Syntax.DeclarativeCoreMatchScrutineesOutcomeProperties
import Solcore.Syntax.Parser.Statement.Match

/-! Executable outcomes for requiring nonempty Core match scrutinees. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Successful executable conversion preserves the exact nonempty elements
and input remainder. -/
theorem requireScrutinees_success_ordinary_sound
    (values : DelimitedList Expr) {input output : State}
    {scrutinees : NonemptyDelimitedList Expr}
    (result : requireScrutinees values input = .ok scrutinees output) :
    DeclarativeGrammar.RequireScrutineesOrdinaryParses values
      input.declarativeRemainder scrutinees output.declarativeRemainder := by
  rcases values with ⟨span, elements⟩
  unfold requireScrutinees at result
  cases elementsEq : elements with
  | nil => simp [elementsEq, rejectAt] at result
  | cons head tail =>
      simp only [elementsEq, pure] at result
      cases result
      exact .parsed

/-- Executable rejection occurs exactly for an empty element list and retains
the complete input state. -/
theorem requireScrutinees_reject_ordinary_sound
    (values : DelimitedList Expr) {input rejected : State} {failure : Failure}
    (result : requireScrutinees values input = .reject failure rejected) :
    DeclarativeGrammar.RequireScrutineesRejects values
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases values with ⟨span, elements⟩
  unfold requireScrutinees at result
  cases elementsEq : elements with
  | nil =>
      simp only [elementsEq] at result
      unfold rejectAt at result
      cases result
      exact .empty rfl
  | cons head tail => simp [elementsEq, pure] at result

/-- Package both executable nonempty-conversion outcomes. -/
theorem requireScrutinees_ordinaryOutcome_sound
    (values : DelimitedList Expr) :
    (∀ {input output : State}
      {scrutinees : NonemptyDelimitedList Expr},
      requireScrutinees values input = .ok scrutinees output →
        DeclarativeGrammar.RequireScrutineesOrdinaryParses values
          input.declarativeRemainder scrutinees
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      requireScrutinees values input = .reject failure rejected →
        DeclarativeGrammar.RequireScrutineesRejects values
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨requireScrutinees_success_ordinary_sound values,
    requireScrutinees_reject_ordinary_sound values⟩

/-- Re-export deterministic nonempty-conversion outcomes. -/
theorem requireScrutinees_ordinaryOutcomeSpec
    (values : DelimitedList Expr) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.RequireScrutineesOrdinaryParses values)
      (DeclarativeGrammar.RequireScrutineesRejects values) :=
  DeclarativeGrammar.requireScrutineesDeterministicOutcomeSpec values

end Solcore.Syntax.Parser.MatchInternals
