import Solcore.Syntax.Parser.TermCanonicalProperties
import Solcore.Syntax.Parser.TermRecursiveFuelTotalityProperties

/-! Totality of the dynamically fueled public Core statement parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- The recursive adequacy budgets have their expected one-step statement lag. -/
theorem coreTotalityFuels_closedForm : ∀ fuel,
    coreExpressionTotalityFuel fuel = fuel ∧
    corePatternTotalityFuel fuel = fuel ∧
    coreStatementTotalityFuel fuel = fuel.pred := by
  intro fuel
  induction fuel with
  | zero =>
      simp [coreExpressionTotalityFuel, corePatternTotalityFuel,
        coreStatementTotalityFuel]
  | succ fuel inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨expressionFuel, patternFuel, statementFuel⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [coreExpressionTotalityFuel, expressionFuel, statementFuel]
        cases fuel <;> simp
      · rw [corePatternTotalityFuel, patternFuel, expressionFuel]
        simp
      · rw [coreStatementTotalityFuel, statementLayerFuel, expressionFuel,
          patternFuel, statementFuel]
        cases fuel <;> simp [MatchInternals.matchStatementFuel]

/-- Two units above the token count leave one unit of statement adequacy. -/
theorem coreStatementTotalityFuel_add_two (remainingCount : Nat) :
    coreStatementTotalityFuel (remainingCount + 2) =
      remainingCount + 1 := by
  rw [(coreTotalityFuels_closedForm (remainingCount + 2)).2.2]
  simp

end Solcore.Syntax.Parser.TermInternals

namespace Solcore.Syntax.Parser

/-- The public statement parser is ordinary on every valid input. -/
theorem statement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid statement := by
  intro input inputValid
  let contract := TermInternals.coreRecursiveWithFuel_fuelTotalityContract
    CoreStatement.ValidFor TermInternals.canonicalStatementClosure
      (input.remainingCount + 2)
  have adequate : input.remainingCount <
      TermInternals.coreStatementTotalityFuel
        (input.remainingCount + 2) := by
    rw [TermInternals.coreStatementTotalityFuel_add_two]
    omega
  simpa only [statement] using
    contract.statement.ordinary input inputValid adequate

/-- Public statement syntax/state laws paired with unconditional totality. -/
theorem statement_totalityContract :
    TermInternals.StatementTotalityContract CoreStatement.ValidFor
      statement := {
  toStatementParserContract := statement_canonical_contract
  invariantFree := statement_invariantFreeOnValid
}

/-- No internal invariant can escape public statement parsing. -/
theorem statement_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    statement input ≠ .invariant error :=
  statement_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
