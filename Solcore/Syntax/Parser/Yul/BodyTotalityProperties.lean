import Solcore.Syntax.Parser.Yul.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.StatementRecursiveFuelTotalityProperties

/-! Valid-input totality for the public braced inline-Yul body parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public recursive Yul statements satisfy the strict loop-element contract. -/
theorem yulStatement_elementTotalityContract :
    ElementTotalityContract yulStatement := {
  validFor := yulStatement_totalityContract.validFor.mono
    (fun _ _ _ => trivial)
  preservesTokenWindow :=
    yulStatement_totalityContract.preservesTokenWindow
  cursorLtOnSuccess := yulStatement_cursor_lt_onSuccess
  invariantFree := yulStatement_ne_invariant
}

/-- The production-sized block loop always has an ordinary valid-input reply. -/
theorem yulBody_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ body final, yulBody input = .ok body final) ∨
      (∃ failure final, yulBody input = .reject failure final) := by
  let statementFuel := input.remainingCount + 1
  let statementContract : FuelElementTotalityContract yulStatement
      statementFuel := {
    validFor := yulStatement_elementTotalityContract.validFor
    preservesTokenWindow :=
      yulStatement_elementTotalityContract.preservesTokenWindow
    cursorLtOnSuccess :=
      yulStatement_elementTotalityContract.cursorLtOnSuccess
    ordinary := fun state stateValid _ => yulStatement_ordinary state stateValid
  }
  simpa only [yulBody] using
    yulBlock_ordinary_of_statementFuel yulStatement statementFuel
      statementContract input inputValid (by
        simp only [statementFuel]
        omega)

theorem yulBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulBody :=
  yulBody_ordinary

theorem yulBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    yulBody input ≠ .invariant error :=
  yulBody_invariantFreeOnValid.ne_invariant input inputValid error

/-- A successful public body consumes its opening brace. -/
theorem yulBody_cursor_lt_onSuccess
    {input final : State} {body : YulParsedBlock}
    (parsed : yulBody input = .ok body final) :
    input.cursor < final.cursor := by
  unfold yulBody at parsed
  exact yulBlock_cursor_lt_onSuccess yulStatement
    yulStatement_preservesTokensOnSuccess parsed

/-- Complete loop, state-window, progress, and totality laws for `yulBody`. -/
theorem yulBody_elementTotalityContract :
    ElementTotalityContract yulBody := {
  validFor := yulBody_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := yulBody_preservesTokenWindow
  cursorLtOnSuccess := yulBody_cursor_lt_onSuccess
  invariantFree := yulBody_ne_invariant
}

end Solcore.Syntax.Parser
