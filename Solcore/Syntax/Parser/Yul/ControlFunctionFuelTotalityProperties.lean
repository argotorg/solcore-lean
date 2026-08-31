import Solcore.Syntax.Parser.Yul.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.SignatureTotalityProperties
import Solcore.Syntax.Parser.Yul.StatementFallbackFuelTotalityProperties

/-! Fuel-aware totality for Yul block wrappers and function definitions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FuelYulStatementTotalityContract

/-- Add strict progress to view a Yul statement contract as a block element. -/
theorem fuelElementTotalityContract {parser : Parser YulStmt} {fuel : Nat}
    (contract : FuelYulStatementTotalityContract parser fuel)
    (strict : ∀ {input final : State} {value : YulStmt},
      parser input = .ok value final → input.cursor < final.cursor) :
    FuelElementTotalityContract parser fuel := {
  validFor := contract.validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := contract.preservesTokenWindow
  cursorLtOnSuccess := strict
  ordinary := contract.ordinary
}

end FuelYulStatementTotalityContract

private theorem bind_cursor_lt_onSuccess_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input middle : State} {value : alpha},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value,
      Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok firstValue middle => next firstValue middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

/-- A block wrapper has exactly the ordinary outcomes of its parsed block. -/
theorem yulBlockStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ value final, yulBlockStatement statement input = .ok value final) ∨
    (∃ failure final,
      yulBlockStatement statement input = .reject failure final) := by
  rcases (yulBlock_fuelElementTotalityContract statement statementFuel
      contract).ordinary input inputValid adequate with
    ⟨block, final, result⟩ | ⟨failure, final, result⟩
  · exact Or.inl ⟨{ span := block.span, value := .block block.body }, final,
      by simp only [yulBlockStatement, bind, result, pure]⟩
  · exact Or.inr ⟨failure, final, by
      simp only [yulBlockStatement, bind, result]⟩

theorem yulBlockStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    yulBlockStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulBlockStatement_ordinary_of_statementFuel statement statementFuel
      contract input inputValid adequate with
    ⟨value, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful block wrapper consumes its opening brace. -/
theorem yulBlockStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulBlockStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulBlockStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (yulBlock_cursor_lt_onSuccess statement statementPreserves) ?_ parsed
  intro block
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Package a recursive block wrapper with full Yul statement laws. -/
theorem yulBlockStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulBlockStatement statement)
      (statementFuel + 1) := by
  let element := contract.fuelElementTotalityContract statementStrict
  exact {
    toYulStatementParserContracts := {
      validFor := yulBlockStatement_validFor statement contract.validFor
        contract.preservesTokens
      preservesTokens := yulBlockStatement_preservesTokensOnSuccess statement
        contract.preservesTokens
      cursorMonotone := yulBlockStatement_cursorMonotoneOnSuccess statement
        contract.preservesTokens
      startsAtToken := yulBlockStatement_startsAtCurrentTokenOnSuccess statement
        contract.preservesTokens
    }
    preservesTokenWindow := yulBlockStatement_preservesTokenWindow statement
      contract.preservesTokenWindow
    ordinary := yulBlockStatement_ordinary_of_statementFuel statement
      statementFuel element
  }

/--
The function keyword, name, and parameter list spend three units before the
body block needs its one-unit wrapper around recursive statement fuel.
-/
theorem yulFunctionStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 4) :
    (∃ value final, yulFunctionStatement statement input = .ok value final) ∨
    (∃ failure final,
      yulFunctionStatement statement input = .reject failure final) := by
  rcases (keyword_ordinary .functionKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .functionKw .yulStatement input
      inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .functionKw
      .yulStatement input
    rw [markerResult] at markerWindow
    have afterMarkerBudget :
        afterMarker.remainingCount < statementFuel + 3 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .functionKw)
          .yulStatement (· == .keyword .functionKw) markerResult) (by omega)
    rcases yulName_ordinary afterMarker with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameReply := yulName_validFor afterMarker markerReply.2.1
      rw [nameResult] at nameReply
      have nameWindow := yulName_preservesTokenWindow afterMarker
      rw [nameResult] at nameWindow
      have afterNameBudget : afterName.remainingCount < statementFuel + 2 :=
        remainingCount_lt_after_strict_progress nameReply.2.1 nameWindow.2
          (yulName_cursor_lt_onSuccess nameResult) (by omega)
      rcases yulParameters_ordinary afterName nameReply.2.1 with
        ⟨parameters, afterParameters, parametersResult⟩ |
        ⟨failure, rejected, parametersResult⟩
      · have parametersReply := yulParameters_validFor afterName
          nameReply.2.1
        rw [parametersResult] at parametersReply
        have parametersWindow := yulParameters_preservesTokenWindow afterName
        rw [parametersResult] at parametersWindow
        have afterParametersBudget :
            afterParameters.remainingCount < statementFuel + 1 :=
          remainingCount_lt_after_strict_progress parametersReply.2.1
            parametersWindow.2
              (yulParameters_cursor_lt_onSuccess parametersResult) (by omega)
        rcases yulReturns_ordinary afterParameters parametersReply.2.1 with
          ⟨returns, afterReturns, returnsResult⟩ |
          ⟨failure, rejected, returnsResult⟩
        · have returnsReply := yulReturns_validFor afterParameters
            parametersReply.2.1
          rw [returnsResult] at returnsReply
          have returnsWindow := yulReturns_preservesTokenWindow afterParameters
          rw [returnsResult] at returnsWindow
          have bodyBudget : afterReturns.remainingCount < statementFuel + 1 :=
            remainingCount_lt_of_cursor_le returnsWindow.2
              (yulReturns_cursorMonotoneOnSuccess afterParameters returns
                afterReturns returnsResult) afterParametersBudget
          rcases (yulBlock_fuelElementTotalityContract statement statementFuel
              contract).ordinary afterReturns returnsReply.2.1 bodyBudget with
            ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover marker.span body.span
                value := .functionDef name parameters returns body.body
              }, final, by
                simp only [yulFunctionStatement, bind, markerResult,
                  nameResult, parametersResult, returnsResult, bodyResult,
                  pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [yulFunctionStatement, bind, markerResult, nameResult,
                parametersResult, returnsResult, bodyResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [yulFunctionStatement, bind, markerResult, nameResult,
              parametersResult, returnsResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [yulFunctionStatement, bind, markerResult, nameResult,
            parametersResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulFunctionStatement, bind, markerResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulFunctionStatement, bind, markerResult]⟩

theorem yulFunctionStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 4)
    (error : ParserInvariantError) :
    yulFunctionStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulFunctionStatement_ordinary_of_statementFuel statement
      statementFuel contract input inputValid adequate with
    ⟨value, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful function definition consumes its leading keyword. -/
theorem yulFunctionStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulFunctionStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulFunctionStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .functionKw)
      .yulStatement (· == .keyword .functionKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulName_cursorMonotoneOnSuccess
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    yulParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess yulReturns_cursorMonotoneOnSuccess
  intro returns
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Package a recursive function definition with full Yul statement laws. -/
theorem yulFunctionStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulFunctionStatement statement)
      (statementFuel + 4) := by
  let element := contract.fuelElementTotalityContract statementStrict
  exact {
    toYulStatementParserContracts := {
      validFor := yulFunctionStatement_validFor statement contract.validFor
        contract.preservesTokens
      preservesTokens := yulFunctionStatement_preservesTokensOnSuccess statement
        contract.preservesTokens
      cursorMonotone := yulFunctionStatement_cursorMonotoneOnSuccess statement
        contract.preservesTokens
      startsAtToken := yulFunctionStatement_startsAtCurrentTokenOnSuccess
        statement
    }
    preservesTokenWindow := yulFunctionStatement_preservesTokenWindow statement
      contract.preservesTokenWindow
    ordinary := yulFunctionStatement_ordinary_of_statementFuel statement
      statementFuel element
  }

end Solcore.Syntax.Parser
