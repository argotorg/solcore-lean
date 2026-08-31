import Solcore.Syntax.Parser.Yul.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.ExpressionRecursiveTotalityProperties
import Solcore.Syntax.Parser.Yul.StatementFallbackFuelTotalityProperties

/-! Fuel-aware totality for inline-Yul `if` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

private theorem yulIfStatement_weakValidFor
    (statement : Parser YulStmt)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement) :
    (yulIfStatement statement).ValidFor (fun _ _ => True) := by
  unfold yulIfStatement
  apply Parser.bind_validFor (keyword_validFor .ifKw .yulStatement)
  intro marker
  apply Parser.bind_validFor yulExpression_elementTotalityContract.validFor
  intro condition
  apply Parser.bind_validFor
    (yulBlock_validFor (fun _ _ => True) statement statementValid
      statementWindow.preservesTokensOnSuccess)
  intro body
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/--
The keyword and condition spend two units before the block needs its one-unit
wrapper around recursive statement fuel.
-/
theorem yulIfStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 3) :
    (∃ value next, yulIfStatement statement input = .ok value next) ∨
    (∃ failure next,
      yulIfStatement statement input = .reject failure next) := by
  rcases (keyword_ordinary .ifKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .ifKw .yulStatement input
      inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .ifKw .yulStatement
      input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .ifKw) .yulStatement
        (· == .keyword .ifKw) markerResult
    have conditionBudget :
        afterMarker.remainingCount < statementFuel + 2 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    have expressionFree : Parser.InvariantFreeOnValid yulExpression :=
      Parser.invariantFreeOnValid_of_ne_invariant
        yulExpression_elementTotalityContract.invariantFree
    rcases expressionFree afterMarker markerReply.2.1 with
      ⟨condition, afterCondition, conditionResult⟩ |
      ⟨failure, rejected, conditionResult⟩
    · have conditionReply := yulExpression_validFor afterMarker
        markerReply.2.1
      rw [conditionResult] at conditionReply
      have conditionWindow :=
        yulExpression_elementTotalityContract.preservesTokenWindow afterMarker
      rw [conditionResult] at conditionWindow
      have conditionProgress :=
        yulExpression_elementTotalityContract.cursorLtOnSuccess
          conditionResult
      have bodyBudget :
          afterCondition.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress conditionReply.2.1
          conditionWindow.2 conditionProgress (by omega)
      let blockContract := yulBlock_fuelElementTotalityContract statement
        statementFuel statementContract
      rcases blockContract.ordinary afterCondition conditionReply.2.1
          bodyBudget with
        ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨{
            span := SourceSpan.cover marker.span body.span
            value := .ifThen condition body.body
          }, final, by
            simp only [yulIfStatement, bind, markerResult, conditionResult,
              bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [yulIfStatement, bind, markerResult, conditionResult,
            bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulIfStatement, bind, markerResult, conditionResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulIfStatement, bind, markerResult]⟩

theorem yulIfStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 3)
    (error : ParserInvariantError) :
    yulIfStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulIfStatement_ordinary_of_statementFuel statement statementFuel
      statementContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful Yul `if` consumes its leading keyword. -/
theorem yulIfStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulIfStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulIfStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .ifKw)
      .yulStatement (· == .keyword .ifKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- The strict loop contract for one fuel-bounded Yul `if` branch. -/
theorem yulIfStatement_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulIfStatement statement)
      (statementFuel + 3) := {
  validFor := yulIfStatement_weakValidFor statement
    statementContract.validFor statementContract.preservesTokenWindow
  preservesTokenWindow := yulIfStatement_preservesTokenWindow statement
    yulExpression_elementTotalityContract.preservesTokenWindow
      statementContract.preservesTokenWindow
  cursorLtOnSuccess := yulIfStatement_cursor_lt_onSuccess statement
    statementContract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := yulIfStatement_ordinary_of_statementFuel statement
    statementFuel statementContract
}

/-- Package full Yul statement laws together with the same fuel proof. -/
theorem yulIfStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulIfStatement statement)
      (statementFuel + 3) := by
  let statementElement : FuelElementTotalityContract statement
      statementFuel := {
    validFor := statementContract.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := statementContract.preservesTokenWindow
    cursorLtOnSuccess := statementStrict
    ordinary := statementContract.ordinary
  }
  exact {
    toYulStatementParserContracts := {
      validFor := yulIfStatement_validFor statement yulExpression_validFor
        yulExpression_startsAtCurrentTokenOnSuccess
        yulExpression_preservesTokensOnSuccess
        yulExpression_cursorMonotoneOnSuccess statementContract.validFor
          statementContract.preservesTokens
      preservesTokens := yulIfStatement_preservesTokensOnSuccess statement
        yulExpression_preservesTokensOnSuccess
          statementContract.preservesTokens
      cursorMonotone := yulIfStatement_cursorMonotoneOnSuccess statement
        yulExpression_cursorMonotoneOnSuccess
          statementContract.preservesTokens
      startsAtToken := yulIfStatement_startsAtCurrentTokenOnSuccess statement
    }
    preservesTokenWindow := yulIfStatement_preservesTokenWindow statement
      yulExpression_preservesTokenWindow
        statementContract.preservesTokenWindow
    ordinary := yulIfStatement_ordinary_of_statementFuel statement
      statementFuel statementElement
  }

end Solcore.Syntax.Parser
