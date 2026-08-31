import Solcore.Syntax.Parser.Yul.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.ExpressionRecursiveTotalityProperties
import Solcore.Syntax.Parser.Yul.StatementFallbackFuelTotalityProperties

/-! Fuel-aware totality for inline-Yul `for` statements. -/

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

private theorem yulForStatement_weakValidFor
    (statement : Parser YulStmt)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement) :
    (yulForStatement statement).ValidFor (fun _ _ => True) := by
  let blockValid := yulBlock_validFor (fun _ _ => True) statement
    statementValid statementWindow.preservesTokensOnSuccess
  unfold yulForStatement
  apply Parser.bind_validFor (keyword_validFor .forKw .yulStatement)
  intro marker
  apply Parser.bind_validFor blockValid
  intro initializer
  apply Parser.bind_validFor yulExpression_elementTotalityContract.validFor
  intro condition
  apply Parser.bind_validFor blockValid
  intro post
  apply Parser.bind_validFor blockValid
  intro body
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/--
The leading keyword spends the one unit needed to enter the first block;
subsequent strict block progress preserves enough fuel for every later block.
-/
theorem yulForStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2) :
    (∃ value next, yulForStatement statement input = .ok value next) ∨
    (∃ failure next,
      yulForStatement statement input = .reject failure next) := by
  let blockContract := yulBlock_fuelElementTotalityContract statement
    statementFuel statementContract
  have expressionFree : Parser.InvariantFreeOnValid yulExpression :=
    Parser.invariantFreeOnValid_of_ne_invariant
      yulExpression_elementTotalityContract.invariantFree
  rcases (keyword_ordinary .forKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .forKw .yulStatement input
      inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .forKw .yulStatement
      input
    rw [markerResult] at markerWindow
    have initializerBudget :
        afterMarker.remainingCount < statementFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .forKw) .yulStatement
          (· == .keyword .forKw) markerResult) adequate
    rcases blockContract.ordinary afterMarker markerReply.2.1
        initializerBudget with
      ⟨initializer, afterInitializer, initializerResult⟩ |
      ⟨failure, rejected, initializerResult⟩
    · have initializerReply := blockContract.validFor afterMarker
        markerReply.2.1
      rw [initializerResult] at initializerReply
      have initializerWindow := blockContract.preservesTokenWindow afterMarker
      rw [initializerResult] at initializerWindow
      have conditionBudget :
          afterInitializer.remainingCount < statementFuel :=
        remainingCount_lt_after_strict_progress initializerReply.2.1
          initializerWindow.2
          (blockContract.cursorLtOnSuccess initializerResult)
          initializerBudget
      rcases expressionFree afterInitializer initializerReply.2.1 with
        ⟨condition, afterCondition, conditionResult⟩ |
        ⟨failure, rejected, conditionResult⟩
      · have conditionReply := yulExpression_validFor afterInitializer
          initializerReply.2.1
        rw [conditionResult] at conditionReply
        have conditionWindow :=
          yulExpression_elementTotalityContract.preservesTokenWindow
            afterInitializer
        rw [conditionResult] at conditionWindow
        have conditionProgress :=
          yulExpression_elementTotalityContract.cursorLtOnSuccess
            conditionResult
        have postBudget :
            afterCondition.remainingCount < statementFuel + 1 := by
          have preserved :
              afterCondition.remainingCount < statementFuel :=
            remainingCount_lt_of_cursor_le conditionWindow.2
              (Nat.le_of_lt conditionProgress) conditionBudget
          omega
        rcases blockContract.ordinary afterCondition conditionReply.2.1
            postBudget with
          ⟨post, afterPost, postResult⟩ |
          ⟨failure, rejected, postResult⟩
        · have postReply := blockContract.validFor afterCondition
            conditionReply.2.1
          rw [postResult] at postReply
          have postWindow := blockContract.preservesTokenWindow afterCondition
          rw [postResult] at postWindow
          have bodyBudget :
              afterPost.remainingCount < statementFuel + 1 := by
            have spent : afterPost.remainingCount < statementFuel :=
              remainingCount_lt_after_strict_progress postReply.2.1
                postWindow.2 (blockContract.cursorLtOnSuccess postResult)
                  postBudget
            omega
          rcases blockContract.ordinary afterPost postReply.2.1 bodyBudget with
            ⟨body, final, bodyResult⟩ |
            ⟨failure, rejected, bodyResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover marker.span body.span
                value := .forLoop initializer.body condition post.body
                  body.body
              }, final, by
                simp only [yulForStatement, bind, markerResult,
                  initializerResult, conditionResult, postResult, bodyResult,
                  pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [yulForStatement, bind, markerResult,
                initializerResult, conditionResult, postResult, bodyResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [yulForStatement, bind, markerResult,
              initializerResult, conditionResult, postResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [yulForStatement, bind, markerResult, initializerResult,
            conditionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulForStatement, bind, markerResult, initializerResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulForStatement, bind, markerResult]⟩

theorem yulForStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2)
    (error : ParserInvariantError) :
    yulForStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulForStatement_ordinary_of_statementFuel statement statementFuel
      statementContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful Yul `for` consumes its leading keyword. -/
theorem yulForStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulForStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulForStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .forKw)
      .yulStatement (· == .keyword .forKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro post
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- The strict loop contract for one fuel-bounded Yul `for` branch. -/
theorem yulForStatement_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulForStatement statement)
      (statementFuel + 2) := {
  validFor := yulForStatement_weakValidFor statement
    statementContract.validFor statementContract.preservesTokenWindow
  preservesTokenWindow := yulForStatement_preservesTokenWindow statement
    yulExpression_elementTotalityContract.preservesTokenWindow
      statementContract.preservesTokenWindow
  cursorLtOnSuccess := yulForStatement_cursor_lt_onSuccess statement
    statementContract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := yulForStatement_ordinary_of_statementFuel statement
    statementFuel statementContract
}

/-- Package full Yul statement laws together with the same fuel proof. -/
theorem yulForStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulForStatement statement)
      (statementFuel + 2) := by
  let statementElement : FuelElementTotalityContract statement
      statementFuel := {
    validFor := statementContract.validFor.mono (fun _ _ _ => trivial)
    preservesTokenWindow := statementContract.preservesTokenWindow
    cursorLtOnSuccess := statementStrict
    ordinary := statementContract.ordinary
  }
  exact {
    toYulStatementParserContracts := {
      validFor := yulForStatement_validFor statement yulExpression_validFor
        yulExpression_preservesTokensOnSuccess
        yulExpression_cursorMonotoneOnSuccess statementContract.validFor
          statementContract.preservesTokens
      preservesTokens := yulForStatement_preservesTokensOnSuccess statement
        yulExpression_preservesTokensOnSuccess
          statementContract.preservesTokens
      cursorMonotone := yulForStatement_cursorMonotoneOnSuccess statement
        yulExpression_cursorMonotoneOnSuccess
          statementContract.preservesTokens
      startsAtToken := yulForStatement_startsAtCurrentTokenOnSuccess statement
    }
    preservesTokenWindow := yulForStatement_preservesTokenWindow statement
      yulExpression_preservesTokenWindow
        statementContract.preservesTokenWindow
    ordinary := yulForStatement_ordinary_of_statementFuel statement
      statementFuel statementElement
  }

end Solcore.Syntax.Parser
