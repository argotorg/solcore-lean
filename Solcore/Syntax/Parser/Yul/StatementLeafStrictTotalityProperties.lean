import Solcore.Syntax.Parser.Yul.StatementLeafTotalityProperties

/-! Strict progress and complete contracts for inline-Yul statement leaves. -/

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

/-- A successful `let` statement consumes its leading keyword. -/
theorem yulLetStatement_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulLetStatement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulLetStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .letKw)
      .yulStatement (· == .keyword .letKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulNames_cursorMonotoneOnSuccess
  intro names
  apply Parser.bind_cursorMonotoneOnSuccess
    yulLetInitializer_cursorMonotoneOnSuccess
  intro initializer
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful assignment consumes its first target name. -/
theorem yulAssignment_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulAssignment input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulAssignment at parsed
  apply bind_cursor_lt_onSuccess_of_first yulNames_cursor_lt_onSuccess ?_
    parsed
  intro names
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .colonEqual .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    yulExpression_cursorMonotoneOnSuccess
  intro expression
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful expression statement consumes its expression's first token. -/
theorem yulExpressionStatement_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulExpressionStatement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulExpressionStatement at parsed
  apply bind_cursor_lt_onSuccess_of_first
    yulExpression_cursor_lt_onSuccess ?_ parsed
  intro expression
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful source-level `return(...)` consumes its keyword. -/
theorem yulReturnBuiltin_cursor_lt_onSuccess
    {input final : State} {value : YulStmt}
    (parsed : yulReturnBuiltin input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulReturnBuiltin at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .returnKw)
      .yulStatement (· == .keyword .returnKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      yulExpression .yulExpression .yul)
  intro arguments
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Every successful keyword-only control statement consumes its keyword. -/
theorem yulControlToken_cursor_lt_onSuccess
    (keywordValue : HardKeyword) (result : YulStmtValue)
    {input final : State} {value : YulStmt}
    (parsed : yulControlToken keywordValue result input = .ok value final) :
    input.cursor < final.cursor := by
  unfold yulControlToken at parsed
  apply bind_cursor_lt_onSuccess_of_first
    (fun parsedKeyword => acceptToken_cursor_lt_onSuccess
      (.keyword keywordValue) .yulStatement
        (· == .keyword keywordValue) parsedKeyword) ?_ parsed
  intro marker
  exact Parser.pure_cursorMonotoneOnSuccess _

namespace YulStatementTotalityContract

/-- Adding strict progress turns a Yul syntax contract into a loop contract. -/
theorem elementTotalityContract {parser : Parser YulStmt}
    (contract : YulStatementTotalityContract parser)
    (strict : ∀ {input final : State} {value : YulStmt},
      parser input = .ok value final → input.cursor < final.cursor) :
    ElementTotalityContract parser := {
  validFor := contract.validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := contract.preservesTokenWindow
  cursorLtOnSuccess := strict
  invariantFree := contract.invariantFree.ne_invariant
}

end YulStatementTotalityContract

theorem yulLetStatement_elementTotalityContract :
    ElementTotalityContract yulLetStatement :=
  YulStatementTotalityContract.elementTotalityContract
    yulLetStatement_totalityContract yulLetStatement_cursor_lt_onSuccess

theorem yulAssignment_elementTotalityContract :
    ElementTotalityContract yulAssignment :=
  YulStatementTotalityContract.elementTotalityContract
    yulAssignment_totalityContract yulAssignment_cursor_lt_onSuccess

theorem yulExpressionStatement_elementTotalityContract :
    ElementTotalityContract yulExpressionStatement :=
  YulStatementTotalityContract.elementTotalityContract
    yulExpressionStatement_totalityContract
      yulExpressionStatement_cursor_lt_onSuccess

theorem yulReturnBuiltin_elementTotalityContract :
    ElementTotalityContract yulReturnBuiltin :=
  YulStatementTotalityContract.elementTotalityContract
    yulReturnBuiltin_totalityContract yulReturnBuiltin_cursor_lt_onSuccess

theorem yulControlToken_elementTotalityContract
    (keywordValue : HardKeyword) (result : YulStmtValue)
    (resultValid : ∀ file span, span.ValidFor file →
      YulStmt.ValidFor file { span, value := result }) :
    ElementTotalityContract (yulControlToken keywordValue result) :=
  YulStatementTotalityContract.elementTotalityContract
    (yulControlToken_totalityContract keywordValue result resultValid)
      (yulControlToken_cursor_lt_onSuccess keywordValue result)

theorem yulLeaveControl_elementTotalityContract :
    ElementTotalityContract (yulControlToken .leaveKw .leave) :=
  yulControlToken_elementTotalityContract .leaveKw .leave
    (fun _ _ => YulStmt.ValidFor.leave)

theorem yulBreakControl_elementTotalityContract :
    ElementTotalityContract (yulControlToken .breakKw .break) :=
  yulControlToken_elementTotalityContract .breakKw .break
    (fun _ _ => YulStmt.ValidFor.break)

theorem yulContinueControl_elementTotalityContract :
    ElementTotalityContract (yulControlToken .continueKw .continue) :=
  yulControlToken_elementTotalityContract .continueKw .continue
    (fun _ _ => YulStmt.ValidFor.continue)

end Solcore.Syntax.Parser
