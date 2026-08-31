import Solcore.Syntax.Parser.Yul.Control
import Solcore.Syntax.YulStatementValidity

/-! Compositional contracts for canonical inline-Yul control statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulBind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

/--
Yul `if` parsing preserves the keyword, condition, block, and every statement
retained by the block.  The fixed expression parser remains an explicit
dependency until its recursive fuel proof is closed.
-/
theorem yulIfStatement_validFor (statement : Parser YulStmt)
    (expressionValid : yulExpression.ValidFor YulExpr.ValidFor)
    (expressionStarts :
      Parser.StartsAtCurrentTokenOnSuccess yulExpression (·.span))
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    (yulIfStatement statement).ValidFor YulStmt.ValidFor := by
  have weak : (yulIfStatement statement).ValidFor (fun _ _ => True) := by
    unfold yulIfStatement
    apply Parser.bind_validFor (keyword_validFor .ifKw .yulStatement)
    intro marker
    apply Parser.bind_validFor expressionValid
    intro condition
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulIfStatement statement input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulIfStatement at stages
      rcases yulBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨condition, afterCondition, conditionResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := keyword_validFor .ifKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      have conditionValid := expressionValid afterMarker markerValid.2.1
      rw [conditionResult] at conditionValid
      have bodyValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterCondition conditionValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have conditionValidInput :
          YulExpr.ValidFor input.file condition := by
        simpa [markerValid.2.2] using conditionValid.1
      have bodySpanValid : body.span.ValidFor input.file := by
        simpa [conditionValid.2.2, markerValid.2.2] using bodyValid.1.1
      have bodyStatementsValid :
          ∀ retained ∈ body.body, YulStmt.ValidFor input.file retained := by
        intro retained member
        simpa [conditionValid.2.2, markerValid.2.2] using
          bodyValid.1.2 retained member
      have markerShape := acceptToken_ok_state_shape
        (.keyword .ifKw) .yulStatement (· == .keyword .ifKw) markerResult
      have markerAdvanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      rcases expressionStarts afterMarker condition afterCondition
          conditionResult with
        ⟨conditionToken, conditionFound, conditionStart⟩
      rcases yulBlock_startsAtCurrentTokenOnSuccess statement
          statementPreserves afterCondition body afterBody bodyResult with
        ⟨openingToken, openingFound, openingStart⟩
      have markerAt :=
        State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      have openingAtInput :
          input.tokens[afterCondition.cursor]? = some openingToken := by
        have openingAt :=
          State.getElem?_eq_some_of_peek?_eq_some openingFound
        have conditionTokens := expressionPreserves afterMarker condition
          afterCondition conditionResult
        have markerTokens := keyword_preservesTokensOnSuccess .ifKw
          .yulStatement input marker afterMarker markerResult
        simpa [conditionTokens, markerTokens] using openingAt
      have markerOrder :
          marker.span.endByte ≤ condition.span.startByte ∧
            marker.span.endByte ≤ body.span.startByte := by
        constructor
        · rw [← conditionStart]
          exact inputValid.consumed_end_le_peek_start_after_advance
            markerAdvanced conditionFound
        · rw [← openingStart]
          apply inputValid.token_end_le_token_start_of_getElem?_lt
            markerAt openingAtInput
          have conditionCursor := expressionMonotone afterMarker condition
            afterCondition conditionResult
          have cursorAfterMarker :
              input.cursor + 1 ≤ afterCondition.cursor := by
            simpa [markerShape.2] using conditionCursor
          omega
      have outerValid :
          (SourceSpan.cover marker.span body.span).ValidFor input.file := by
        apply SourceSpan.cover_validFor markerSpanValid bodySpanValid
        exact Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerOrder.2 bodySpanValid.2.1)
      cases finished
      exact ⟨YulStmt.ValidFor.ifThen outerValid conditionValidInput
          bodyStatementsValid,
        weakResult.2.1, weakResult.2.2⟩

/-- Yul `if` parsing preserves the immutable lexer token carrier. -/
theorem yulIfStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulIfStatement statement) := by
  unfold yulIfStatement
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .ifKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess expressionPreserves
  intro condition
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_preservesTokensOnSuccess _

/-- Yul `if` parsing never moves the parser cursor backwards. -/
theorem yulIfStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulIfStatement statement) := by
  unfold yulIfStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .ifKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess expressionMonotone
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul `if` statement starts at its current `if` token. -/
theorem yulIfStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulIfStatement statement) (·.span) := by
  unfold yulIfStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .ifKw) .yulStatement (· == .keyword .ifKw))
  intro marker input value final parsed
  rcases yulBind_ok_components parsed with
    ⟨condition, afterCondition, _conditionResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

end Solcore.Syntax.Parser
