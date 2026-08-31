import Solcore.Syntax.Parser.Yul.ControlForFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.ControlFunctionFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.ControlIfFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.ControlSwitchStatementFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.StatementChoiceFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.StatementLeafStrictTotalityProperties

/-! Fuel-aware totality for the complete ordered Yul statement dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem recognized_sameFuel_contract
    (primary fallback : Parser YulStmt) (fuel : Nat)
    (primaryContract : FuelYulStatementTotalityContract primary fuel)
    (fallbackContract : FuelYulStatementTotalityContract fallback fuel) :
    FuelYulStatementTotalityContract
      (recognizedYulStatementOrFallback primary fallback) fuel := by
  simpa using recognizedYulStatementOrFallback_fuelTotalityContract
    primary fallback fuel fuel primaryContract fallbackContract

private theorem stateChoice_sameFuel_contract
    (condition : State → Bool) (first second : Parser YulStmt) (fuel : Nat)
    (firstContract : FuelYulStatementTotalityContract first fuel)
    (secondContract : FuelYulStatementTotalityContract second fuel) :
    FuelYulStatementTotalityContract
      (fun input => if condition input then first input else second input)
      fuel := by
  simpa using stateChoice_fuelTotalityContract condition first second fuel fuel
    firstContract secondContract

private theorem orElse_sameFuel_contract
    (first second : Parser YulStmt) (fuel : Nat)
    (firstContract : FuelYulStatementTotalityContract first fuel)
    (secondContract : FuelYulStatementTotalityContract second fuel) :
    FuelYulStatementTotalityContract (orElse first second) fuel := by
  simpa using orElse_fuelTotalityContract first second fuel fuel firstContract
    secondContract

/-- Every ordered Yul statement branch is ordinary at one common outer fuel. -/
theorem yulStatementCore_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulStatementCore statement)
      (statementFuel + 1) := by
  let commonFuel := statementFuel + 1
  have fallbackContract : FuelYulStatementTotalityContract
      yulExpressionStatement commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      yulExpressionStatement_totalityContract commonFuel
  have blockContract : FuelYulStatementTotalityContract
      (yulBlockStatement statement) commonFuel := by
    simpa [commonFuel] using yulBlockStatement_fuelTotalityContract statement
      statementFuel statementContract statementStrict
  have letContract : FuelYulStatementTotalityContract yulLetStatement
      commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      yulLetStatement_totalityContract commonFuel
  have ifContract : FuelYulStatementTotalityContract
      (yulIfStatement statement) commonFuel :=
    (yulIfStatement_fuelTotalityContract statement statementFuel
      statementContract statementStrict).weaken (by
        simp only [commonFuel]
        omega)
  have forContract : FuelYulStatementTotalityContract
      (yulForStatement statement) commonFuel :=
    (yulForStatement_fuelTotalityContract statement statementFuel
      statementContract statementStrict).weaken (by
        simp only [commonFuel]
        omega)
  have switchContract : FuelYulStatementTotalityContract
      (yulSwitchStatement statement) commonFuel :=
    (yulSwitchStatement_fuelTotalityContract statement statementFuel
      statementContract statementStrict).weaken (by
        simp only [commonFuel]
        omega)
  have functionContract : FuelYulStatementTotalityContract
      (yulFunctionStatement statement) commonFuel :=
    (yulFunctionStatement_fuelTotalityContract statement statementFuel
      statementContract statementStrict).weaken (by
        simp only [commonFuel]
        omega)
  have returnContract : FuelYulStatementTotalityContract yulReturnBuiltin
      commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      yulReturnBuiltin_totalityContract commonFuel
  have leaveContract : FuelYulStatementTotalityContract
      (yulControlToken .leaveKw .leave) commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      (yulControlToken_totalityContract .leaveKw .leave
        (fun _ _ => YulStmt.ValidFor.leave)) commonFuel
  have breakContract : FuelYulStatementTotalityContract
      (yulControlToken .breakKw .break) commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      (yulControlToken_totalityContract .breakKw .break
        (fun _ _ => YulStmt.ValidFor.break)) commonFuel
  have continueContract : FuelYulStatementTotalityContract
      (yulControlToken .continueKw .continue) commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      (yulControlToken_totalityContract .continueKw .continue
        (fun _ _ => YulStmt.ValidFor.continue)) commonFuel
  have assignmentContract : FuelYulStatementTotalityContract yulAssignment
      commonFuel :=
    FuelYulStatementTotalityContract.ofTotality
      yulAssignment_totalityContract commonFuel
  change FuelYulStatementTotalityContract (yulStatementCore statement)
    commonFuel
  unfold yulStatementCore
  apply stateChoice_sameFuel_contract
  · exact recognized_sameFuel_contract _ _ commonFuel blockContract
      fallbackContract
  · apply stateChoice_sameFuel_contract
    · exact recognized_sameFuel_contract _ _ commonFuel letContract
        fallbackContract
    · apply stateChoice_sameFuel_contract
      · exact recognized_sameFuel_contract _ _ commonFuel ifContract
          fallbackContract
      · apply stateChoice_sameFuel_contract
        · exact recognized_sameFuel_contract _ _ commonFuel forContract
            fallbackContract
        · apply stateChoice_sameFuel_contract
          · exact recognized_sameFuel_contract _ _ commonFuel switchContract
              fallbackContract
          · apply stateChoice_sameFuel_contract
            · exact recognized_sameFuel_contract _ _ commonFuel
                functionContract fallbackContract
            · apply stateChoice_sameFuel_contract
              · exact recognized_sameFuel_contract _ _ commonFuel
                  returnContract fallbackContract
              · apply stateChoice_sameFuel_contract
                · exact recognized_sameFuel_contract _ _ commonFuel
                    leaveContract fallbackContract
                · apply stateChoice_sameFuel_contract
                  · exact recognized_sameFuel_contract _ _ commonFuel
                      breakContract fallbackContract
                  · apply stateChoice_sameFuel_contract
                    · exact recognized_sameFuel_contract _ _ commonFuel
                        continueContract fallbackContract
                    · apply stateChoice_sameFuel_contract
                      · exact orElse_sameFuel_contract _ _ commonFuel
                          assignmentContract fallbackContract
                      · exact fallbackContract

/-- Every successful ordered Yul statement branch consumes at least one token. -/
theorem yulStatementCore_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulStatementCore statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulStatementCore at parsed
  dsimp only at parsed
  split at parsed
  · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
      _ _ (yulBlockStatement_cursor_lt_onSuccess statement
        statementPreserves) yulExpressionStatement_cursor_lt_onSuccess parsed
  · split at parsed
    · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
        _ _ yulLetStatement_cursor_lt_onSuccess
          yulExpressionStatement_cursor_lt_onSuccess parsed
    · split at parsed
      · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
          _ _ (yulIfStatement_cursor_lt_onSuccess statement
            statementPreserves) yulExpressionStatement_cursor_lt_onSuccess
              parsed
      · split at parsed
        · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
            _ _ (yulForStatement_cursor_lt_onSuccess statement
              statementPreserves) yulExpressionStatement_cursor_lt_onSuccess
                parsed
        · split at parsed
          · exact recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
              _ _ (yulSwitchStatement_cursor_lt_onSuccess statement
                statementPreserves) yulExpressionStatement_cursor_lt_onSuccess
                  parsed
          · split at parsed
            · exact
                recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                  _ _ (yulFunctionStatement_cursor_lt_onSuccess statement
                    statementPreserves)
                      yulExpressionStatement_cursor_lt_onSuccess parsed
            · split at parsed
              · exact
                  recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                    _ _ yulReturnBuiltin_cursor_lt_onSuccess
                      yulExpressionStatement_cursor_lt_onSuccess parsed
              · split at parsed
                · exact
                    recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                      _ _ (yulControlToken_cursor_lt_onSuccess .leaveKw .leave)
                        yulExpressionStatement_cursor_lt_onSuccess parsed
                · split at parsed
                  · exact
                      recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                        _ _ (yulControlToken_cursor_lt_onSuccess .breakKw .break)
                          yulExpressionStatement_cursor_lt_onSuccess parsed
                  · split at parsed
                    · exact
                        recognizedYulStatementOrFallback_cursor_lt_onSuccess_of_strict
                          _ _ (yulControlToken_cursor_lt_onSuccess .continueKw
                            .continue) yulExpressionStatement_cursor_lt_onSuccess
                              parsed
                    · split at parsed
                      · exact orElse_cursor_lt_onSuccess_of_strict _ _
                          yulAssignment_cursor_lt_onSuccess
                            yulExpressionStatement_cursor_lt_onSuccess parsed
                      · exact yulExpressionStatement_cursor_lt_onSuccess parsed

end Solcore.Syntax.Parser
