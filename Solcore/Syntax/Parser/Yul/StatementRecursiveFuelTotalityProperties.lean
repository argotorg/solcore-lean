import Solcore.Syntax.Parser.Yul.StatementCoreFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.StatementRecoveryFuelTotalityProperties

/-! Totality for the recursive and public inline-Yul statement parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful fuel-indexed statement consumes at least one token. -/
theorem yulStatementWithFuel_cursor_lt_onSuccess :
    ∀ fuel, ∀ {input final : State} {value : YulStmt},
      yulStatementWithFuel fuel input = .ok value final →
        input.cursor < final.cursor := by
  intro fuel
  cases fuel with
  | zero =>
      intro input final value parsed
      simp [yulStatementWithFuel] at parsed
  | succ fuel =>
      intro input final value parsed
      apply yulStatementLayer_cursor_lt_onSuccess_of_terminated
        (yulStatementWithFuel fuel) ?_ parsed
      intro terminatedInput terminatedFinal terminatedValue terminatedParsed
      exact yulStatementTerminated_cursor_lt_onSuccess_of_core
        (yulStatementWithFuel fuel)
        (yulStatementCore_cursor_lt_onSuccess (yulStatementWithFuel fuel)
          (yulStatementWithFuel_preservesTokensOnSuccess fuel))
        terminatedParsed

/--
The syntax recursion index is also the exact valid-input totality bound.
The zero parser is vacuously total below zero; each layer adds one unit.
-/
theorem yulStatementWithFuel_fuelTotalityContract :
    ∀ fuel, FuelYulStatementTotalityContract
      (yulStatementWithFuel fuel) fuel := by
  intro fuel
  induction fuel with
  | zero =>
      exact {
        toYulStatementParserContracts := {
          validFor := yulStatementWithFuel_validFor 0
          preservesTokens := yulStatementWithFuel_preservesTokensOnSuccess 0
          cursorMonotone := yulStatementWithFuel_cursorMonotoneOnSuccess 0
          startsAtToken :=
            yulStatementWithFuel_startsAtCurrentTokenOnSuccess 0
        }
        preservesTokenWindow := yulStatementWithFuel_preservesTokenWindow 0
        ordinary := by
          intro input inputValid adequate
          omega
      }
  | succ fuel inductionHypothesis =>
      let nested := yulStatementWithFuel fuel
      let coreContract := yulStatementCore_fuelTotalityContract nested fuel
        inductionHypothesis
        (yulStatementWithFuel_cursor_lt_onSuccess fuel)
      let terminatedContract := yulStatementTerminated_fuelTotalityContract
        nested (fuel + 1) (yulStatementWithFuel_validFor fuel)
          (yulStatementWithFuel_preservesTokensOnSuccess fuel) coreContract
      have layerContract := yulStatementLayer_fuelTotalityContract nested
        (fuel + 1) (yulStatementWithFuel_validFor fuel)
          (yulStatementWithFuel_preservesTokensOnSuccess fuel)
            coreContract.preservesTokenWindow terminatedContract
      simpa only [yulStatementWithFuel, nested] using layerContract

/-- The production-selected recursive fuel always yields an ordinary reply. -/
theorem yulStatement_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ value next, yulStatement input = .ok value next) ∨
      (∃ failure next, yulStatement input = .reject failure next) := by
  unfold yulStatement
  exact (yulStatementWithFuel_fuelTotalityContract
    (input.remainingCount + 1)).ordinary input inputValid (by omega)

theorem yulStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulStatement :=
  yulStatement_ordinary

theorem yulStatement_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    yulStatement input ≠ .invariant error :=
  yulStatement_invariantFreeOnValid.ne_invariant input inputValid error

/-- Public statement success inherits strict progress from its chosen index. -/
theorem yulStatement_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulStatement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulStatement at parsed
  exact yulStatementWithFuel_cursor_lt_onSuccess
    (input.remainingCount + 1) parsed

/-- Complete syntax, state, and valid-input totality for public Yul statements. -/
theorem yulStatement_totalityContract :
    YulStatementTotalityContract yulStatement := {
  toYulStatementParserContracts := {
    validFor := yulStatement_validFor
    preservesTokens := yulStatement_preservesTokensOnSuccess
    cursorMonotone := yulStatement_cursorMonotoneOnSuccess
    startsAtToken := yulStatement_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulStatement_preservesTokenWindow
  invariantFree := yulStatement_invariantFreeOnValid
}

end Solcore.Syntax.Parser
