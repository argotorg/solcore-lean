import Solcore.Syntax.DeclarativeCoreMatchStatementGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Deterministic outcomes for requiring nonempty Core match scrutinees. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev RequireScrutineesOrdinaryParses := RequireScrutineesParses

/-- Empty parsed scrutinees reject without consuming any further token. -/
inductive RequireScrutineesRejects (values : DelimitedList Syntax.Expr) :
    Remainder → Remainder → Prop where
  | empty {input : Remainder} (emptyValues : values.elements = []) :
      RequireScrutineesRejects values input input

/-- Nonempty scrutinee conversion has one output remainder. -/
theorem RequireScrutineesOrdinaryParses.output_unique
    {values : DelimitedList Syntax.Expr} {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : RequireScrutineesOrdinaryParses values input left afterLeft)
    (rightParsed : RequireScrutineesOrdinaryParses values input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed
  cases rightParsed
  rfl

/-- Empty scrutinee rejection excludes nonempty conversion. -/
theorem RequireScrutineesRejects.disjointOrdinary
    {values : DelimitedList Syntax.Expr} {input rejected : Remainder}
    (rejection : RequireScrutineesRejects values input rejected) :
    ¬ ∃ scrutinees output,
      RequireScrutineesOrdinaryParses values input scrutinees output := by
  rintro ⟨scrutinees, output, successful⟩
  cases rejection with
  | empty emptyValues =>
      cases successful
      contradiction

/-- Requiring nonempty scrutinees is a deterministic pure outcome. -/
theorem requireScrutineesDeterministicOutcomeSpec
    (values : DelimitedList Syntax.Expr) :
    DeterministicOutcomeSpec
      (RequireScrutineesOrdinaryParses values)
      (RequireScrutineesRejects values) where
  successOutputUnique := RequireScrutineesOrdinaryParses.output_unique
  successRejectDisjoint := RequireScrutineesRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
