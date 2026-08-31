import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.Statement.MatchProperties

/-! Totality for the nonempty Core-match scrutinee conversion. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Scrutinee conversion either retains a nonempty list or rejects empty input. -/
theorem requireScrutinees_ordinary (values : DelimitedList Expr) :
    Parser.Ordinary (requireScrutinees values) := by
  intro input
  unfold requireScrutinees
  cases values.elements with
  | nil => exact Or.inr ⟨_, input, rfl⟩
  | cons head tail => exact Or.inl ⟨_, input, rfl⟩

/-- Scrutinee conversion exposes no internal invariant on valid input. -/
theorem requireScrutinees_invariantFreeOnValid
    (values : DelimitedList Expr) :
    Parser.InvariantFreeOnValid (requireScrutinees values) :=
  (requireScrutinees_ordinary values).invariantFreeOnValid

/-- Empty or nonempty scrutinee conversion can never return an invariant. -/
theorem requireScrutinees_ne_invariant (values : DelimitedList Expr)
    (input : State) (error : ParserInvariantError) :
    requireScrutinees values input ≠ .invariant error :=
  (requireScrutinees_ordinary values).ne_invariant input error

end Solcore.Syntax.Parser.MatchInternals
