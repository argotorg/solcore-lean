import Solcore.Syntax.Parser.Yul.ControlSwitchDefaultFuelTotalityProperties

/-! Fuel-aware totality for complete inline-Yul `switch` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem switch_bind_cursor_lt_of_first {alpha beta : Type}
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

/--
The default-only path spends four strict tokens before recursive statements;
case arms spend at least one more. This common bound covers both paths.
-/
theorem yulSwitchStatement_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 4) :
    (∃ value next, yulSwitchStatement statement input = .ok value next) ∨
      (∃ failure next,
        yulSwitchStatement statement input = .reject failure next) := by
  let statementElement := statementContract.fuelElementTotalityContract
    statementStrict
  let casesContract := yulCases_fuelTotalityContract statement statementFuel
    statementContract statementStrict
  let defaultContract := optionalYulDefault_fuelTotalityContract statement
    statementFuel statementElement
  rcases (keyword_ordinary .switchKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .switchKw .yulStatement input
      inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .switchKw
      .yulStatement input
    rw [markerResult] at markerWindow
    have expressionBudget :
        afterMarker.remainingCount < statementFuel + 3 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .switchKw) .yulStatement
          (· == .keyword .switchKw) markerResult) adequate
    have expressionFree : Parser.InvariantFreeOnValid yulExpression :=
      Parser.invariantFreeOnValid_of_ne_invariant
        yulExpression_elementTotalityContract.invariantFree
    rcases expressionFree afterMarker markerReply.2.1 with
      ⟨scrutinee, afterExpression, expressionResult⟩ |
      ⟨failure, rejected, expressionResult⟩
    · have expressionReply := yulExpression_elementTotalityContract.validFor
        afterMarker markerReply.2.1
      rw [expressionResult] at expressionReply
      have expressionWindow :=
        yulExpression_elementTotalityContract.preservesTokenWindow afterMarker
      rw [expressionResult] at expressionWindow
      have casesBudget :
          afterExpression.remainingCount < statementFuel + 2 :=
        remainingCount_lt_after_strict_progress expressionReply.2.1
          expressionWindow.2
            (yulExpression_elementTotalityContract.cursorLtOnSuccess
              expressionResult) expressionBudget
      rcases casesContract.ordinary afterExpression expressionReply.2.1
          (by omega) with
        ⟨cases, afterCases, casesResult⟩ |
        ⟨failure, rejected, casesResult⟩
      · have casesReply := casesContract.validFor afterExpression
          expressionReply.2.1
        rw [casesResult] at casesReply
        have casesWindow := casesContract.preservesTokenWindow afterExpression
        rw [casesResult] at casesWindow
        have defaultBudget :
            afterCases.remainingCount < statementFuel + 2 :=
          remainingCount_lt_of_cursor_le casesWindow.2
            (casesContract.cursorMonotoneOnSuccess afterExpression cases
              afterCases casesResult) casesBudget
        rcases defaultContract.ordinary afterCases casesReply.2.1
            defaultBudget with
          ⟨defaultBody, afterDefault, defaultResult⟩ |
          ⟨failure, rejected, defaultResult⟩
        · cases cases with
          | cons head tail =>
              cases defaultBody with
              | none =>
                  let endSpan := match (head :: tail).reverse with
                    | last :: _ => last.span
                    | [] => scrutinee.span
                  exact Or.inl ⟨{
                      span := SourceSpan.cover marker.span endSpan
                      value := .switch scrutinee { head, tail } none
                    }, afterDefault, by
                    simp only [yulSwitchStatement, bind, markerResult,
                      expressionResult, casesResult, defaultResult, pure,
                      Option.map_none, endSpan]
                    rfl⟩
              | some body =>
                  exact Or.inl ⟨{
                      span := SourceSpan.cover marker.span body.span
                      value := .switch scrutinee { head, tail }
                        (some body.body)
                    }, afterDefault, by
                    simp only [yulSwitchStatement, bind, markerResult,
                      expressionResult, casesResult, defaultResult, pure,
                      Option.map_some]⟩
          | nil =>
              cases defaultBody with
              | none =>
                  let span := SourceSpan.cover marker.span scrutinee.span
                  let diagnostic : ParseDiagnostic := {
                    span
                    kind := .constraintViolation .yulSwitchRequiresCase
                  }
                  exact Or.inl ⟨{ span, value := .error },
                    afterDefault.emit diagnostic, by
                    simp only [yulSwitchStatement, bind, markerResult,
                      expressionResult, casesResult, defaultResult,
                      List.reverse_nil, emitDiagnostic, modifyState, pure,
                      span, diagnostic]⟩
              | some body =>
                  let span := SourceSpan.cover marker.span body.span
                  let diagnostic : ParseDiagnostic := {
                    span
                    kind := .constraintViolation .yulSwitchRequiresCase
                  }
                  exact Or.inl ⟨{ span, value := .error },
                    afterDefault.emit diagnostic, by
                    simp only [yulSwitchStatement, bind, markerResult,
                      expressionResult, casesResult, defaultResult,
                      emitDiagnostic, modifyState, pure, span, diagnostic]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [yulSwitchStatement, bind, markerResult,
              expressionResult, casesResult, defaultResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [yulSwitchStatement, bind, markerResult,
            expressionResult, casesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [yulSwitchStatement, bind, markerResult, expressionResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulSwitchStatement, bind, markerResult]⟩

theorem yulSwitchStatement_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 4)
    (error : ParserInvariantError) :
    yulSwitchStatement statement input ≠ .invariant error := by
  intro failed
  rcases yulSwitchStatement_ordinary_of_statementFuel statement statementFuel
      statementContract statementStrict input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Every successful Yul switch consumes its leading keyword. -/
theorem yulSwitchStatement_cursor_lt_onSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input final : State} {value : YulStmt}
    (parsed : yulSwitchStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulSwitchStatement at parsed
  apply switch_bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .switchKw)
      .yulStatement (· == .keyword .switchKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro scrutinee
  apply Parser.bind_cursorMonotoneOnSuccess
  · intro input cases next result
    exact yulCases_cursorMonotoneOnSuccess statement
      (input.remainingCount + 1) [] input cases next result
  intro cases
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalYulDefault_cursorMonotoneOnSuccess statement statementPreserves)
  intro defaultBody
  cases cases with
  | cons head tail => exact Parser.pure_cursorMonotoneOnSuccess _
  | nil =>
      apply Parser.bind_cursorMonotoneOnSuccess
        (emitDiagnostic_cursorMonotoneOnSuccess _)
      intro emitted
      exact Parser.pure_cursorMonotoneOnSuccess _

theorem yulSwitchStatement_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelElementTotalityContract (yulSwitchStatement statement)
      (statementFuel + 4) := {
  validFor := (yulSwitchStatement_validFor statement
    statementContract.validFor statementContract.preservesTokens).mono
      (fun _ _ _ => trivial)
  preservesTokenWindow := yulSwitchStatement_preservesTokenWindow statement
    statementContract.preservesTokenWindow
  cursorLtOnSuccess := yulSwitchStatement_cursor_lt_onSuccess statement
    statementContract.preservesTokens
  ordinary := yulSwitchStatement_ordinary_of_statementFuel statement
    statementFuel statementContract statementStrict
}

theorem yulSwitchStatement_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract :
      FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    FuelYulStatementTotalityContract (yulSwitchStatement statement)
      (statementFuel + 4) := {
  toYulStatementParserContracts := {
    validFor := yulSwitchStatement_validFor statement
      statementContract.validFor statementContract.preservesTokens
    preservesTokens := yulSwitchStatement_preservesTokensOnSuccess statement
      statementContract.preservesTokens
    cursorMonotone := yulSwitchStatement_cursorMonotoneOnSuccess statement
      statementContract.preservesTokens
    startsAtToken := yulSwitchStatement_startsAtCurrentTokenOnSuccess statement
  }
  preservesTokenWindow := yulSwitchStatement_preservesTokenWindow statement
    statementContract.preservesTokenWindow
  ordinary := yulSwitchStatement_ordinary_of_statementFuel statement
    statementFuel statementContract statementStrict
}

end Solcore.Syntax.Parser
