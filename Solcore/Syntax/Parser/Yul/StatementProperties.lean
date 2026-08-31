import Solcore.Syntax.Parser.Yul.Statement
import Solcore.Syntax.Parser.Yul.ExpressionProperties
import Solcore.Syntax.YulStatementValidity

/-! Compositional contracts for canonical inline-Yul leaf statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem yulExpr_span_valid {file : SourceFile} {value : YulExpr}
    (valid : YulExpr.ValidFor file value) : value.span.ValidFor file := by
  cases valid <;> assumption

private theorem yulStatementBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
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
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- A Yul assignment preserves its names, value, and covering range. -/
theorem yulAssignment_validFor :
    yulAssignment.ValidFor YulStmt.ValidFor := by
  have weak : yulAssignment.ValidFor (fun _ _ => True) := by
    unfold yulAssignment
    apply Parser.bind_validFor yulNames_validFor
    intro names
    apply Parser.bind_validFor (symbol_validFor .colonEqual .yulStatement)
    intro marker
    apply Parser.bind_validFor yulExpression_validFor
    intro value
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulAssignment input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulAssignment at stages
      rcases yulStatementBind_ok_components stages with
        ⟨names, afterNames, namesResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨value, afterValue, valueResult, finished⟩
      have namesValid := yulNames_validFor input inputValid
      rw [namesResult] at namesValid
      have markerValid := symbol_validFor .colonEqual .yulStatement
        afterNames namesValid.2.1
      rw [markerResult] at markerValid
      have valueValid := yulExpression_validFor afterMarker markerValid.2.1
      rw [valueResult] at valueValid
      have namesSpanValid : names.span.ValidFor input.file := namesValid.1.1
      have valueValidInput : YulExpr.ValidFor input.file value := by
        simpa [markerValid.2.2, namesValid.2.2] using valueValid.1
      have valueSpanValid : value.span.ValidFor input.file :=
        yulExpr_span_valid valueValidInput
      rcases yulNames_startsAtCurrentTokenOnSuccess input names afterNames
          namesResult with ⟨firstToken, firstFound, namesStart⟩
      rcases yulExpression_startsAtCurrentTokenOnSuccess afterMarker value
          afterValue valueResult with ⟨valueToken, valueFound, valueStart⟩
      have firstAt := State.getElem?_eq_some_of_peek?_eq_some firstFound
      have valueAt : input.tokens[afterMarker.cursor]? = some valueToken := by
        have foundAt := State.getElem?_eq_some_of_peek?_eq_some valueFound
        have namesTokens := yulNames_preservesTokensOnSuccess input names
          afterNames namesResult
        have markerTokens := symbol_preservesTokensOnSuccess .colonEqual
          .yulStatement afterNames marker afterMarker markerResult
        simpa [markerTokens, namesTokens] using foundAt
      have tokenOrder : firstToken.span.endByte ≤ valueToken.span.startByte := by
        apply inputValid.token_end_le_token_start_of_getElem?_lt firstAt valueAt
        have namesProgress :=
          (yulNames_ok_state_shape namesResult).choose_spec.2.2.2
        have markerShape := symbol_ok_state_shape .colonEqual .yulStatement
          markerResult
        exact Nat.lt_trans namesProgress (by simp [markerShape.2])
      have outerOrdered : names.span.startByte ≤ value.span.endByte := by
        have firstValid := inputValid.peek?_span_validFor firstFound
        exact Nat.le_trans (by simpa [namesStart] using firstValid.2.1)
          (Nat.le_trans tokenOrder
            (by simpa [valueStart] using valueSpanValid.2.1))
      have outerValid := SourceSpan.cover_validFor namesSpanValid
        valueSpanValid outerOrdered
      cases finished
      exact ⟨YulStmt.ValidFor.assign outerValid namesValid.1.2
          valueValidInput,
        weakResult.2.1, weakResult.2.2⟩

/-- A Yul assignment preserves the immutable token carrier. -/
theorem yulAssignment_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_preservesTokensOnSuccess
    yulNames_preservesTokensOnSuccess
  intro names
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .colonEqual .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess
    yulExpression_preservesTokensOnSuccess
  intro value
  exact Parser.pure_preservesTokensOnSuccess _

/-- A Yul assignment never rewinds the parser cursor. -/
theorem yulAssignment_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_cursorMonotoneOnSuccess yulNames_cursorMonotoneOnSuccess
  intro names
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .colonEqual .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro value
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul assignment starts at its first target name. -/
theorem yulAssignment_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulAssignment (·.span) := by
  unfold yulAssignment
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    yulNames_startsAtCurrentTokenOnSuccess
  intro names input statement final parsed
  rcases yulStatementBind_ok_components parsed with
    ⟨marker, afterMarker, _markerResult, rest⟩
  rcases yulStatementBind_ok_components rest with
    ⟨value, afterValue, _valueResult, finished⟩
  cases finished
  rfl

/-- An expression in statement position retains recursive provenance. -/
theorem yulExpressionStatement_validFor :
    yulExpressionStatement.ValidFor YulStmt.ValidFor := by
  unfold yulExpressionStatement
  apply Parser.bind_validFor_of_value yulExpression_validFor
  intro expression input inputValid expressionValid
  exact ⟨YulStmt.ValidFor.expression (yulExpr_span_valid expressionValid)
      expressionValid,
    inputValid, rfl⟩

/-- Expression statements preserve every ordinary token window. -/
theorem yulExpressionStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow yulExpressionStatement := by
  unfold yulExpressionStatement
  apply Parser.bind_preservesTokenWindow yulExpression_preservesTokenWindow
  intro expression
  exact Parser.pure_preservesTokenWindow _

theorem yulExpressionStatement_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulExpressionStatement :=
  yulExpressionStatement_preservesTokenWindow.preservesTokensOnSuccess

/-- Expression statements never rewind the parser cursor. -/
theorem yulExpressionStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulExpressionStatement := by
  unfold yulExpressionStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro expression
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful expression statement starts at its expression token. -/
theorem yulExpressionStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulExpressionStatement (·.span) := by
  unfold yulExpressionStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    yulExpression_startsAtCurrentTokenOnSuccess
  intros
  cases ‹_ = Reply.ok _ _›
  rfl

/-- A keyword-only Yul control statement retains its keyword range. -/
theorem yulControlToken_validFor (value : HardKeyword)
    (result : YulStmtValue)
    (resultValid : ∀ file span, span.ValidFor file →
      YulStmt.ValidFor file { span, value := result }) :
    (yulControlToken value result).ValidFor YulStmt.ValidFor := by
  unfold yulControlToken
  apply Parser.bind_validFor_of_value (keyword_validFor value .yulStatement)
  intro marker input inputValid markerValid
  exact ⟨resultValid input.file marker.span markerValid, inputValid, rfl⟩

theorem yulLeaveControl_validFor :
    (yulControlToken .leaveKw .leave).ValidFor YulStmt.ValidFor :=
  yulControlToken_validFor .leaveKw .leave
    (fun _ _ => YulStmt.ValidFor.leave)

theorem yulBreakControl_validFor :
    (yulControlToken .breakKw .break).ValidFor YulStmt.ValidFor :=
  yulControlToken_validFor .breakKw .break
    (fun _ _ => YulStmt.ValidFor.break)

theorem yulContinueControl_validFor :
    (yulControlToken .continueKw .continue).ValidFor YulStmt.ValidFor :=
  yulControlToken_validFor .continueKw .continue
    (fun _ _ => YulStmt.ValidFor.continue)

/-- Keyword-only Yul control statements preserve complete token windows. -/
theorem yulControlToken_preservesTokenWindow (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.PreservesTokenWindow (yulControlToken value result) := by
  unfold yulControlToken
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow value .yulStatement)
  intro marker
  exact Parser.pure_preservesTokenWindow _

theorem yulControlToken_preservesTokensOnSuccess (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.PreservesTokensOnSuccess (yulControlToken value result) :=
  (yulControlToken_preservesTokenWindow value result).preservesTokensOnSuccess

/-- Keyword-only Yul control statements never rewind the cursor. -/
theorem yulControlToken_cursorMonotoneOnSuccess (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.CursorMonotoneOnSuccess (yulControlToken value result) := by
  unfold yulControlToken
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess value .yulStatement)
  intro marker
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A keyword-only Yul control statement starts at its keyword token. -/
theorem yulControlToken_startsAtCurrentTokenOnSuccess (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulControlToken value result) (·.span) := by
  unfold yulControlToken
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword value)
      .yulStatement (· == .keyword value))
  intros
  cases ‹_ = Reply.ok _ _›
  rfl

end Solcore.Syntax.Parser
