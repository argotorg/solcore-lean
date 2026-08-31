import Solcore.Syntax.Parser.Yul.Statement
import Solcore.Syntax.Parser.Yul.ControlSwitchProperties
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

/-- A block statement preserves its braces and every nested statement. -/
theorem yulBlockStatement_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (yulBlockStatement statement).ValidFor YulStmt.ValidFor := by
  unfold yulBlockStatement
  apply Parser.bind_validFor_of_value
    (yulBlock_validFor YulStmt.ValidFor statement statementValid
      statementPreserves)
  intro block input inputValid blockValid
  exact ⟨YulStmt.ValidFor.block blockValid.1 blockValid.2,
    inputValid, rfl⟩

theorem yulBlockStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulBlockStatement statement) := by
  unfold yulBlockStatement
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro block
  exact Parser.pure_preservesTokensOnSuccess _

/-- Block statements preserve the nested parser's ordinary token window. -/
theorem yulBlockStatement_preservesTokenWindow (statement : Parser YulStmt)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (yulBlockStatement statement) := by
  unfold yulBlockStatement
  apply Parser.bind_preservesTokenWindow
    (yulBlock_preservesTokenWindow statement statementShape)
  intro block
  exact Parser.pure_preservesTokenWindow _

theorem yulBlockStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulBlockStatement statement) := by
  unfold yulBlockStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro block
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem yulBlockStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulBlockStatement statement) (·.span) := by
  unfold yulBlockStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (yulBlock_startsAtCurrentTokenOnSuccess statement statementPreserves)
  intros
  cases ‹_ = Reply.ok _ _›
  rfl

/-- A Yul `let` initializer preserves a present expression's provenance. -/
theorem yulLetInitializer_validFor :
    yulLetInitializer.ValidFor (Option.ValidFor YulExpr.ValidFor) := by
  unfold yulLetInitializer
  apply Parser.bind_validFor getState_validFor
  intro state
  split
  · apply Parser.bind_validFor
      (symbol_validFor .colonEqual .yulStatement)
    intro marker
    apply Parser.bind_validFor_of_value yulExpression_validFor
    intro expression input inputValid expressionValid
    exact ⟨expressionValid, inputValid, rfl⟩
  · exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional Yul `let` initialization preserves every token window. -/
theorem yulLetInitializer_preservesTokenWindow :
    Parser.PreservesTokenWindow yulLetInitializer := by
  unfold yulLetInitializer
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro state
  split
  · apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .colonEqual .yulStatement)
    intro marker
    apply Parser.bind_preservesTokenWindow yulExpression_preservesTokenWindow
    intro expression
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow none

/-- Optional Yul `let` initialization never rewinds the cursor. -/
theorem yulLetInitializer_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulLetInitializer := by
  unfold yulLetInitializer
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro state
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .colonEqual .yulStatement)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      yulExpression_cursorMonotoneOnSuccess
    intro expression
    exact Parser.pure_cursorMonotoneOnSuccess _
  · exact Parser.pure_cursorMonotoneOnSuccess none

private theorem yulLetInitializer_some_components {input next : State}
    {expression : YulExpr}
    (parsed : yulLetInitializer input = .ok (some expression) next) :
    ∃ marker afterMarker,
      symbol .colonEqual .yulStatement input = .ok marker afterMarker ∧
        yulExpression afterMarker = .ok expression next := by
  unfold yulLetInitializer at parsed
  rcases yulStatementBind_ok_components parsed with
    ⟨state, afterState, stateResult, rest⟩
  unfold getState at stateResult
  cases stateResult
  split at rest
  · rcases yulStatementBind_ok_components rest with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases yulStatementBind_ok_components rest with
      ⟨value, afterValue, valueResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, markerResult, valueResult⟩
  · cases rest

/-- A Yul `let` declaration preserves names, initializer, and outer range. -/
theorem yulLetStatement_validFor :
    yulLetStatement.ValidFor YulStmt.ValidFor := by
  have weak : yulLetStatement.ValidFor (fun _ _ => True) := by
    unfold yulLetStatement
    apply Parser.bind_validFor (keyword_validFor .letKw .yulStatement)
    intro marker
    apply Parser.bind_validFor yulNames_validFor
    intro names
    apply Parser.bind_validFor yulLetInitializer_validFor
    intro initializer
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulLetStatement input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulLetStatement at stages
      rcases yulStatementBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨names, afterNames, namesResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨initializer, afterInitializer, initializerResult, finished⟩
      have markerValid := keyword_validFor .letKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      have namesValid := yulNames_validFor afterMarker markerValid.2.1
      rw [namesResult] at namesValid
      have initializerValid := yulLetInitializer_validFor afterNames
        namesValid.2.1
      rw [initializerResult] at initializerValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have namesValidInput : YulNameSequence.ValidFor input.file names := by
        simpa [markerValid.2.2] using namesValid.1
      have markerShape := acceptToken_ok_state_shape (.keyword .letKw)
        .yulStatement (· == .keyword .letKw) markerResult
      have markerAdvanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      rcases yulNames_startsAtCurrentTokenOnSuccess afterMarker names
          afterNames namesResult with ⟨firstName, firstFound, namesStart⟩
      cases initializer with
      | none =>
          have markerBeforeNames :=
            inputValid.consumed_end_le_peek_start_after_advance
              markerAdvanced firstFound
          have ordered : marker.span.startByte ≤ names.span.endByte :=
            Nat.le_trans markerSpanValid.2.1
              (Nat.le_trans markerBeforeNames (by
                rw [namesStart]
                exact namesValidInput.1.2.1))
          cases finished
          exact ⟨YulStmt.ValidFor.letDecl
              (SourceSpan.cover_validFor markerSpanValid namesValidInput.1
                ordered)
              namesValidInput.2 trivial,
            weakResult.2.1, weakResult.2.2⟩
      | some expression =>
          rcases yulLetInitializer_some_components initializerResult with
            ⟨assignMarker, afterAssignMarker, assignResult,
              expressionResult⟩
          rcases yulExpression_startsAtCurrentTokenOnSuccess
              afterAssignMarker expression afterInitializer expressionResult with
            ⟨expressionToken, expressionFound, expressionStart⟩
          have markerAt :=
            State.getElem?_eq_some_of_peek?_eq_some markerShape.1
          have expressionAt : input.tokens[afterAssignMarker.cursor]? =
              some expressionToken := by
            have foundAt :=
              State.getElem?_eq_some_of_peek?_eq_some expressionFound
            have keywordTokens := keyword_preservesTokensOnSuccess .letKw
              .yulStatement input marker afterMarker markerResult
            have namesTokens := yulNames_preservesTokensOnSuccess afterMarker
              names afterNames namesResult
            have assignTokens := symbol_preservesTokensOnSuccess .colonEqual
              .yulStatement afterNames assignMarker afterAssignMarker assignResult
            simpa [assignTokens, namesTokens, keywordTokens] using foundAt
          have markerBeforeExpression :
              marker.span.endByte ≤ expressionToken.span.startByte := by
            apply inputValid.token_end_le_token_start_of_getElem?_lt markerAt
              expressionAt
            have namesProgress :=
              (yulNames_ok_state_shape namesResult).choose_spec.2.2.2
            have assignShape := symbol_ok_state_shape .colonEqual .yulStatement
              assignResult
            exact Nat.lt_trans (by simp [markerShape.2])
              (Nat.lt_trans namesProgress (by simp [assignShape.2]))
          have expressionValidInput :
              YulExpr.ValidFor input.file expression := by
            have validAfterNames :
                YulExpr.ValidFor afterNames.file expression := by
              simpa only [Option.ValidFor] using initializerValid.1
            simpa [namesValid.2.2, markerValid.2.2] using validAfterNames
          have expressionSpanValid := yulExpr_span_valid expressionValidInput
          have ordered : marker.span.startByte ≤ expression.span.endByte :=
            Nat.le_trans markerSpanValid.2.1
              (Nat.le_trans markerBeforeExpression (by
                rw [expressionStart]
                exact expressionSpanValid.2.1))
          cases finished
          exact ⟨YulStmt.ValidFor.letDecl
              (SourceSpan.cover_validFor markerSpanValid expressionSpanValid
                ordered)
              namesValidInput.2 expressionValidInput,
            weakResult.2.1, weakResult.2.2⟩

/-- Yul `let` parsing preserves every ordinary token window. -/
theorem yulLetStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow yulLetStatement := by
  unfold yulLetStatement
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .letKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow yulNames_preservesTokenWindow
  intro names
  apply Parser.bind_preservesTokenWindow yulLetInitializer_preservesTokenWindow
  intro initializer
  exact Parser.pure_preservesTokenWindow _

theorem yulLetStatement_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulLetStatement :=
  yulLetStatement_preservesTokenWindow.preservesTokensOnSuccess

/-- Yul `let` parsing never rewinds the cursor. -/
theorem yulLetStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulLetStatement := by
  unfold yulLetStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .letKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulNames_cursorMonotoneOnSuccess
  intro names
  apply Parser.bind_cursorMonotoneOnSuccess
    yulLetInitializer_cursorMonotoneOnSuccess
  intro initializer
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul `let` declaration starts at its `let` token. -/
theorem yulLetStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulLetStatement (·.span) := by
  unfold yulLetStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .letKw)
      .yulStatement (· == .keyword .letKw))
  intro marker input statement final parsed
  rcases yulStatementBind_ok_components parsed with
    ⟨names, afterNames, _namesResult, rest⟩
  rcases yulStatementBind_ok_components rest with
    ⟨initializer, afterInitializer, _initializerResult, finished⟩
  cases finished
  rfl

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

/-- Yul assignments preserve every ordinary token window. -/
theorem yulAssignment_preservesTokenWindow :
    Parser.PreservesTokenWindow yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_preservesTokenWindow yulNames_preservesTokenWindow
  intro names
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .colonEqual .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow yulExpression_preservesTokenWindow
  intro value
  exact Parser.pure_preservesTokenWindow _

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

/-- Yul `return(...)` preserves its synthesized call and argument ranges. -/
theorem yulReturnBuiltin_validFor :
    yulReturnBuiltin.ValidFor YulStmt.ValidFor := by
  have argumentsContract := delimited_validFor YulExpr.ValidFor .leftParen
    .rightParen true yulExpression .yulExpression .yul
    yulExpression_validFor yulExpression_preservesTokensOnSuccess
  have weak : yulReturnBuiltin.ValidFor (fun _ _ => True) := by
    unfold yulReturnBuiltin
    apply Parser.bind_validFor (keyword_validFor .returnKw .yulStatement)
    intro marker
    apply Parser.bind_validFor argumentsContract
    intro arguments
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulReturnBuiltin input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok statement final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulReturnBuiltin at stages
      rcases yulStatementBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulStatementBind_ok_components rest with
        ⟨arguments, afterArguments, argumentsResult, finished⟩
      have markerValid := keyword_validFor .returnKw .yulStatement input
        inputValid
      rw [markerResult] at markerValid
      have argumentsValid := argumentsContract afterMarker markerValid.2.1
      rw [argumentsResult] at argumentsValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have argumentsValidInput :
          DelimitedList.ValidFor YulExpr.ValidFor input.file arguments := by
        simpa [markerValid.2.2] using argumentsValid.1
      have markerShape := acceptToken_ok_state_shape (.keyword .returnKw)
        .yulStatement (· == .keyword .returnKw) markerResult
      have markerAdvanced : input.advance? = some (marker, afterMarker) := by
        unfold State.advance?
        rw [markerShape.1, markerShape.2]
        rfl
      rcases delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen
          true yulExpression .yulExpression .yul afterMarker arguments
          afterArguments argumentsResult with
        ⟨opening, openingFound, argumentsStart⟩
      have markerBeforeArguments :=
        inputValid.consumed_end_le_peek_start_after_advance markerAdvanced
          openingFound
      have ordered : marker.span.startByte ≤ arguments.span.endByte :=
        Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeArguments (by
            rw [argumentsStart]
            exact argumentsValidInput.1.2.1))
      have outerValid := SourceSpan.cover_validFor markerSpanValid
        argumentsValidInput.1 ordered
      have expressionValid : YulExpr.ValidFor input.file {
          span := SourceSpan.cover marker.span arguments.span
          value := .call { span := marker.span, value := "return" } arguments
        } := YulExpr.ValidFor.call outerValid markerSpanValid
          argumentsValidInput.1 argumentsValidInput.2
      cases finished
      exact ⟨YulStmt.ValidFor.expression outerValid expressionValid,
        weakResult.2.1, weakResult.2.2⟩

/-- Yul `return(...)` preserves every ordinary token window. -/
theorem yulReturnBuiltin_preservesTokenWindow :
    Parser.PreservesTokenWindow yulReturnBuiltin := by
  unfold yulReturnBuiltin
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .returnKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftParen .rightParen true yulExpression
      .yulExpression .yul yulExpression_preservesTokenWindow)
  intro arguments
  exact Parser.pure_preservesTokenWindow _

theorem yulReturnBuiltin_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulReturnBuiltin :=
  yulReturnBuiltin_preservesTokenWindow.preservesTokensOnSuccess

/-- Yul `return(...)` never rewinds the parser cursor. -/
theorem yulReturnBuiltin_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulReturnBuiltin := by
  unfold yulReturnBuiltin
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .returnKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
      yulExpression .yulExpression .yul)
  intro arguments
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul `return(...)` starts at its `return` token. -/
theorem yulReturnBuiltin_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulReturnBuiltin (·.span) := by
  unfold yulReturnBuiltin
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .returnKw)
      .yulStatement (· == .keyword .returnKw))
  intro marker input statement final parsed
  rcases yulStatementBind_ok_components parsed with
    ⟨arguments, afterArguments, _argumentsResult, finished⟩
  cases finished
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

/-- Recognized-statement fallback preserves either branch's provenance. -/
theorem recognizedYulStatementOrFallback_validFor {valueValid :
    SourceFile → YulStmt → Prop} (primary fallback : Parser YulStmt)
    (primaryValid : primary.ValidFor valueValid)
    (fallbackValid : fallback.ValidFor valueValid) :
    (recognizedYulStatementOrFallback primary fallback).ValidFor valueValid := by
  intro input inputValid
  have primaryContract := primaryValid input inputValid
  unfold recognizedYulStatementOrFallback
  cases primaryResult : primary input with
  | invariant error => trivial
  | ok value next =>
      rw [primaryResult] at primaryContract
      simpa only [primaryResult] using primaryContract
  | reject failure failedState =>
      rw [primaryResult] at primaryContract
      have fallbackContract := fallbackValid input inputValid
      cases fallbackResult : fallback input with
      | invariant error => trivial
      | reject fallbackFailure fallbackState =>
          simp only [Reply.ValidFor]
          exact ⟨primaryContract.1, inputValid, trivial⟩
      | ok value next =>
          rw [fallbackResult] at fallbackContract
          let reset : State := {
            next with diagnosticsRev := input.diagnosticsRev
          }
          have resetValid : reset.ValidFor := {
            tokens := fallbackContract.2.1.tokens
            cursor_le_endIndex := fallbackContract.2.1.cursor_le_endIndex
            endIndex_le_size := fallbackContract.2.1.endIndex_le_size
            endByte_le_source := fallbackContract.2.1.endByte_le_source
            endByte_boundary := fallbackContract.2.1.endByte_boundary
            diagnosticsRev := by
              intro diagnostic member
              simpa [reset, fallbackContract.2.2] using
                inputValid.diagnosticsRev diagnostic member
          }
          have emittedValid := resetValid.emit_validFor failure.toDiagnostic
            (by simpa [reset, fallbackContract.2.2] using
              failure.toDiagnostic_span_validFor primaryContract.1)
          simp only [Reply.ValidFor]
          exact ⟨fallbackContract.1, emittedValid,
            by simpa [reset, State.emit] using fallbackContract.2.2⟩

/-- Recognized-statement fallback preserves every ordinary token window. -/
theorem recognizedYulStatementOrFallback_preservesTokenWindow
    (primary fallback : Parser YulStmt)
    (primaryShape : Parser.PreservesTokenWindow primary)
    (fallbackShape : Parser.PreservesTokenWindow fallback) :
    Parser.PreservesTokenWindow
      (recognizedYulStatementOrFallback primary fallback) := by
  intro input
  have primaryContract := primaryShape input
  unfold recognizedYulStatementOrFallback
  cases primaryResult : primary input with
  | invariant error => trivial
  | ok value next =>
      rw [primaryResult] at primaryContract
      simpa only [primaryResult] using primaryContract
  | reject failure failedState =>
      have fallbackContract := fallbackShape input
      cases fallbackResult : fallback input with
      | invariant error => trivial
      | reject fallbackFailure fallbackState =>
          simp only [Reply.PreservesTokenWindow]
          exact ⟨trivial, trivial⟩
      | ok value next =>
          rw [fallbackResult] at fallbackContract
          simpa only [primaryResult, fallbackResult, State.emit,
            Reply.PreservesTokenWindow] using fallbackContract

theorem recognizedYulStatementOrFallback_preservesTokensOnSuccess
    (primary fallback : Parser YulStmt)
    (primaryShape : Parser.PreservesTokenWindow primary)
    (fallbackShape : Parser.PreservesTokenWindow fallback) :
    Parser.PreservesTokensOnSuccess
      (recognizedYulStatementOrFallback primary fallback) :=
  (recognizedYulStatementOrFallback_preservesTokenWindow primary fallback
    primaryShape fallbackShape).preservesTokensOnSuccess

/-- Success-only carrier contracts also compose through recognized fallback. -/
theorem recognizedYulStatementOrFallback_preservesTokensOnSuccess_of_success
    (primary fallback : Parser YulStmt)
    (primaryPreserves : Parser.PreservesTokensOnSuccess primary)
    (fallbackPreserves : Parser.PreservesTokensOnSuccess fallback) :
    Parser.PreservesTokensOnSuccess
      (recognizedYulStatementOrFallback primary fallback) := by
  intro input value next result
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have preserved := primaryPreserves input primaryValue afterPrimary
        primaryResult
      cases result
      exact preserved
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have preserved := fallbackPreserves input fallbackValue afterFallback
            fallbackResult
          cases result
          exact preserved

/-- Recognized-statement fallback never rewinds either successful branch. -/
theorem recognizedYulStatementOrFallback_cursorMonotoneOnSuccess
    (primary fallback : Parser YulStmt)
    (primaryMonotone : Parser.CursorMonotoneOnSuccess primary)
    (fallbackMonotone : Parser.CursorMonotoneOnSuccess fallback) :
    Parser.CursorMonotoneOnSuccess
      (recognizedYulStatementOrFallback primary fallback) := by
  intro input value next result
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have monotone := primaryMonotone input primaryValue afterPrimary
        primaryResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have monotone := fallbackMonotone input fallbackValue afterFallback
            fallbackResult
          cases result
          exact monotone

/-- Successful recognized fallback starts at the selected branch's token. -/
theorem recognizedYulStatementOrFallback_startsAtCurrentTokenOnSuccess
    (primary fallback : Parser YulStmt)
    (primaryStarts : Parser.StartsAtCurrentTokenOnSuccess primary (·.span))
    (fallbackStarts : Parser.StartsAtCurrentTokenOnSuccess fallback (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (recognizedYulStatementOrFallback primary fallback) (·.span) := by
  intro input value next result
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have starts := primaryStarts input primaryValue afterPrimary primaryResult
      cases result
      exact starts
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have starts := fallbackStarts input fallbackValue afterFallback
            fallbackResult
          cases result
          exact starts

/-- Contracts needed to compose one recursive Yul statement choice. -/
structure YulStatementParserContracts (parser : Parser YulStmt) : Prop where
  validFor : parser.ValidFor YulStmt.ValidFor
  preservesTokens : Parser.PreservesTokensOnSuccess parser
  cursorMonotone : Parser.CursorMonotoneOnSuccess parser
  startsAtToken : Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

private theorem stateChoice_contracts (condition : State → Bool)
    (first second : Parser YulStmt)
    (firstContracts : YulStatementParserContracts first)
    (secondContracts : YulStatementParserContracts second) :
    YulStatementParserContracts (fun input =>
      if condition input then first input else second input) := {
  validFor := by
    intro input inputValid
    by_cases selected : condition input = true
    · simpa [selected] using firstContracts.validFor input inputValid
    · simpa [selected] using secondContracts.validFor input inputValid
  preservesTokens := by
    intro input value next result
    by_cases selected : condition input = true
    · exact firstContracts.preservesTokens input value next
        (by simpa [selected] using result)
    · exact secondContracts.preservesTokens input value next
        (by simpa [selected] using result)
  cursorMonotone := by
    intro input value next result
    by_cases selected : condition input = true
    · exact firstContracts.cursorMonotone input value next
        (by simpa [selected] using result)
    · exact secondContracts.cursorMonotone input value next
        (by simpa [selected] using result)
  startsAtToken := by
    intro input value next result
    by_cases selected : condition input = true
    · exact firstContracts.startsAtToken input value next
        (by simpa [selected] using result)
    · exact secondContracts.startsAtToken input value next
        (by simpa [selected] using result)
}

private theorem recognized_contracts (primary fallback : Parser YulStmt)
    (primaryContracts : YulStatementParserContracts primary)
    (fallbackContracts : YulStatementParserContracts fallback) :
    YulStatementParserContracts
      (recognizedYulStatementOrFallback primary fallback) := {
  validFor := recognizedYulStatementOrFallback_validFor primary fallback
    primaryContracts.validFor fallbackContracts.validFor
  preservesTokens :=
    recognizedYulStatementOrFallback_preservesTokensOnSuccess_of_success
      primary fallback primaryContracts.preservesTokens
        fallbackContracts.preservesTokens
  cursorMonotone :=
    recognizedYulStatementOrFallback_cursorMonotoneOnSuccess primary fallback
      primaryContracts.cursorMonotone fallbackContracts.cursorMonotone
  startsAtToken :=
    recognizedYulStatementOrFallback_startsAtCurrentTokenOnSuccess
      primary fallback primaryContracts.startsAtToken
        fallbackContracts.startsAtToken
}

private theorem orElse_contracts (first second : Parser YulStmt)
    (firstContracts : YulStatementParserContracts first)
    (secondContracts : YulStatementParserContracts second) :
    YulStatementParserContracts (orElse first second) := {
  validFor := Parser.orElse_validFor firstContracts.validFor
    secondContracts.validFor
  preservesTokens := Parser.orElse_preservesTokensOnSuccess
    firstContracts.preservesTokens secondContracts.preservesTokens
  cursorMonotone := Parser.orElse_cursorMonotoneOnSuccess
    firstContracts.cursorMonotone secondContracts.cursorMonotone
  startsAtToken := Parser.orElse_startsAtCurrentTokenOnSuccess
    firstContracts.startsAtToken secondContracts.startsAtToken
}

/-- All non-terminating Yul statement choices compose from recursive input. -/
theorem yulStatementCore_contracts (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    YulStatementParserContracts (yulStatementCore nested) := by
  let fallbackContracts :
      YulStatementParserContracts yulExpressionStatement :=
    ⟨yulExpressionStatement_validFor,
      yulExpressionStatement_preservesTokensOnSuccess,
      yulExpressionStatement_cursorMonotoneOnSuccess,
      yulExpressionStatement_startsAtCurrentTokenOnSuccess⟩
  have blockContracts :
      YulStatementParserContracts (yulBlockStatement nested) :=
    ⟨yulBlockStatement_validFor nested nestedValid nestedPreserves,
      yulBlockStatement_preservesTokensOnSuccess nested nestedPreserves,
      yulBlockStatement_cursorMonotoneOnSuccess nested nestedPreserves,
      yulBlockStatement_startsAtCurrentTokenOnSuccess nested nestedPreserves⟩
  have letContracts : YulStatementParserContracts yulLetStatement :=
    ⟨yulLetStatement_validFor, yulLetStatement_preservesTokensOnSuccess,
      yulLetStatement_cursorMonotoneOnSuccess,
      yulLetStatement_startsAtCurrentTokenOnSuccess⟩
  have ifContracts :
      YulStatementParserContracts (yulIfStatement nested) :=
    ⟨yulIfStatement_validFor nested yulExpression_validFor
        yulExpression_startsAtCurrentTokenOnSuccess
        yulExpression_preservesTokensOnSuccess
        yulExpression_cursorMonotoneOnSuccess nestedValid nestedPreserves,
      yulIfStatement_preservesTokensOnSuccess nested
        yulExpression_preservesTokensOnSuccess nestedPreserves,
      yulIfStatement_cursorMonotoneOnSuccess nested
        yulExpression_cursorMonotoneOnSuccess nestedPreserves,
      yulIfStatement_startsAtCurrentTokenOnSuccess nested⟩
  have forContracts :
      YulStatementParserContracts (yulForStatement nested) :=
    ⟨yulForStatement_validFor nested yulExpression_validFor
        yulExpression_preservesTokensOnSuccess
        yulExpression_cursorMonotoneOnSuccess nestedValid nestedPreserves,
      yulForStatement_preservesTokensOnSuccess nested
        yulExpression_preservesTokensOnSuccess nestedPreserves,
      yulForStatement_cursorMonotoneOnSuccess nested
        yulExpression_cursorMonotoneOnSuccess nestedPreserves,
      yulForStatement_startsAtCurrentTokenOnSuccess nested⟩
  have switchContracts :
      YulStatementParserContracts (yulSwitchStatement nested) :=
    ⟨yulSwitchStatement_validFor nested nestedValid nestedPreserves,
      yulSwitchStatement_preservesTokensOnSuccess nested nestedPreserves,
      yulSwitchStatement_cursorMonotoneOnSuccess nested nestedPreserves,
      yulSwitchStatement_startsAtCurrentTokenOnSuccess nested⟩
  have functionContracts :
      YulStatementParserContracts (yulFunctionStatement nested) :=
    ⟨yulFunctionStatement_validFor nested nestedValid nestedPreserves,
      yulFunctionStatement_preservesTokensOnSuccess nested nestedPreserves,
      yulFunctionStatement_cursorMonotoneOnSuccess nested nestedPreserves,
      yulFunctionStatement_startsAtCurrentTokenOnSuccess nested⟩
  have returnContracts : YulStatementParserContracts yulReturnBuiltin :=
    ⟨yulReturnBuiltin_validFor, yulReturnBuiltin_preservesTokensOnSuccess,
      yulReturnBuiltin_cursorMonotoneOnSuccess,
      yulReturnBuiltin_startsAtCurrentTokenOnSuccess⟩
  have leaveContracts : YulStatementParserContracts
      (yulControlToken .leaveKw .leave) :=
    ⟨yulLeaveControl_validFor,
      yulControlToken_preservesTokensOnSuccess .leaveKw .leave,
      yulControlToken_cursorMonotoneOnSuccess .leaveKw .leave,
      yulControlToken_startsAtCurrentTokenOnSuccess .leaveKw .leave⟩
  have breakContracts : YulStatementParserContracts
      (yulControlToken .breakKw .break) :=
    ⟨yulBreakControl_validFor,
      yulControlToken_preservesTokensOnSuccess .breakKw .break,
      yulControlToken_cursorMonotoneOnSuccess .breakKw .break,
      yulControlToken_startsAtCurrentTokenOnSuccess .breakKw .break⟩
  have continueContracts : YulStatementParserContracts
      (yulControlToken .continueKw .continue) :=
    ⟨yulContinueControl_validFor,
      yulControlToken_preservesTokensOnSuccess .continueKw .continue,
      yulControlToken_cursorMonotoneOnSuccess .continueKw .continue,
      yulControlToken_startsAtCurrentTokenOnSuccess .continueKw .continue⟩
  have assignmentContracts : YulStatementParserContracts yulAssignment :=
    ⟨yulAssignment_validFor, yulAssignment_preservesTokensOnSuccess,
      yulAssignment_cursorMonotoneOnSuccess,
      yulAssignment_startsAtCurrentTokenOnSuccess⟩
  unfold yulStatementCore
  apply stateChoice_contracts
  · exact recognized_contracts _ _ blockContracts fallbackContracts
  · apply stateChoice_contracts
    · exact recognized_contracts _ _ letContracts fallbackContracts
    · apply stateChoice_contracts
      · exact recognized_contracts _ _ ifContracts fallbackContracts
      · apply stateChoice_contracts
        · exact recognized_contracts _ _ forContracts fallbackContracts
        · apply stateChoice_contracts
          · exact recognized_contracts _ _ switchContracts fallbackContracts
          · apply stateChoice_contracts
            · exact recognized_contracts _ _ functionContracts fallbackContracts
            · apply stateChoice_contracts
              · exact recognized_contracts _ _ returnContracts fallbackContracts
              · apply stateChoice_contracts
                · exact recognized_contracts _ _ leaveContracts fallbackContracts
                · apply stateChoice_contracts
                  · exact recognized_contracts _ _ breakContracts fallbackContracts
                  · apply stateChoice_contracts
                    · exact recognized_contracts _ _ continueContracts
                        fallbackContracts
                    · apply stateChoice_contracts
                      · exact orElse_contracts _ _ assignmentContracts
                          fallbackContracts
                      · exact fallbackContracts

theorem yulStatementCore_validFor (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulStatementCore nested).ValidFor YulStmt.ValidFor :=
  (yulStatementCore_contracts nested nestedValid nestedPreserves).validFor

theorem yulStatementCore_preservesTokensOnSuccess (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulStatementCore nested) :=
  (yulStatementCore_contracts nested nestedValid nestedPreserves).preservesTokens

theorem yulStatementCore_cursorMonotoneOnSuccess (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulStatementCore nested) :=
  (yulStatementCore_contracts nested nestedValid nestedPreserves).cursorMonotone

theorem yulStatementCore_startsAtCurrentTokenOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.StartsAtCurrentTokenOnSuccess (yulStatementCore nested) (·.span) :=
  (yulStatementCore_contracts nested nestedValid nestedPreserves).startsAtToken

/-- Every non-terminating statement choice preserves recursive token windows. -/
theorem yulStatementCore_preservesTokenWindow (nested : Parser YulStmt)
    (nestedShape : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (yulStatementCore nested) := by
  intro input
  unfold yulStatementCore
  split
  · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
      (yulBlockStatement_preservesTokenWindow nested nestedShape)
      yulExpressionStatement_preservesTokenWindow input
  · split
    · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
        yulLetStatement_preservesTokenWindow
        yulExpressionStatement_preservesTokenWindow input
    · split
      · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
          (yulIfStatement_preservesTokenWindow nested
            yulExpression_preservesTokenWindow nestedShape)
          yulExpressionStatement_preservesTokenWindow input
      · split
        · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
            (yulForStatement_preservesTokenWindow nested
              yulExpression_preservesTokenWindow nestedShape)
            yulExpressionStatement_preservesTokenWindow input
        · split
          · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
              (yulSwitchStatement_preservesTokenWindow nested nestedShape)
              yulExpressionStatement_preservesTokenWindow input
          · split
            · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
                (yulFunctionStatement_preservesTokenWindow nested nestedShape)
                yulExpressionStatement_preservesTokenWindow input
            · split
              · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
                  yulReturnBuiltin_preservesTokenWindow
                  yulExpressionStatement_preservesTokenWindow input
              · split
                · exact recognizedYulStatementOrFallback_preservesTokenWindow _ _
                    (yulControlToken_preservesTokenWindow .leaveKw .leave)
                    yulExpressionStatement_preservesTokenWindow input
                · split
                  · exact recognizedYulStatementOrFallback_preservesTokenWindow
                      _ _ (yulControlToken_preservesTokenWindow .breakKw .break)
                      yulExpressionStatement_preservesTokenWindow input
                  · split
                    · exact recognizedYulStatementOrFallback_preservesTokenWindow
                        _ _ (yulControlToken_preservesTokenWindow
                          .continueKw .continue)
                        yulExpressionStatement_preservesTokenWindow input
                    · split
                      · exact Parser.orElse_preservesTokenWindow
                          yulAssignment_preservesTokenWindow
                          yulExpressionStatement_preservesTokenWindow input
                      · exact yulExpressionStatement_preservesTokenWindow input

/-- Optional semicolon parsing preserves a supplied valid statement. -/
theorem optionalYulSemicolon_validForAt (value : YulStmt) (input : State)
    (inputValid : input.ValidFor) (valueValid : YulStmt.ValidFor input.file value) :
    (optionalYulSemicolon value input).ValidFor input YulStmt.ValidFor := by
  unfold optionalYulSemicolon getState
  simp only [bind]
  by_cases present : isSymbol input .semicolon = true
  · simp only [present, if_true]
    cases semicolonResult : symbol .semicolon .yulStatement input with
    | invariant error => trivial
    | reject failure rejected =>
        have valid := symbol_validFor .semicolon .yulStatement input inputValid
        rw [semicolonResult] at valid
        simpa only [bind, semicolonResult, Reply.ValidFor] using valid
    | ok marker next =>
        have valid := symbol_validFor .semicolon .yulStatement input inputValid
        rw [semicolonResult] at valid
        simp only [Reply.ValidFor]
        exact ⟨by simpa [valid.2.2] using valueValid,
          valid.2.1, valid.2.2⟩
  · simp only [present, Bool.false_eq_true, if_false, Reply.ValidFor]
    exact ⟨valueValid, inputValid, rfl⟩

/-- Optional semicolons preserve every ordinary token window. -/
theorem optionalYulSemicolon_preservesTokenWindow (value : YulStmt) :
    Parser.PreservesTokenWindow (optionalYulSemicolon value) := by
  unfold optionalYulSemicolon
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindow
  intro state
  split
  · apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .semicolon .yulStatement)
    intro marker
    exact Parser.pure_preservesTokenWindow value
  · exact Parser.pure_preservesTokenWindow value

/-- Optional semicolons never rewind the parser cursor. -/
theorem optionalYulSemicolon_cursorMonotoneOnSuccess (value : YulStmt) :
    Parser.CursorMonotoneOnSuccess (optionalYulSemicolon value) := by
  unfold optionalYulSemicolon
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro state
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .semicolon .yulStatement)
    intro marker
    exact Parser.pure_cursorMonotoneOnSuccess value
  · exact Parser.pure_cursorMonotoneOnSuccess value

/-- Optional semicolon parsing returns the supplied statement unchanged. -/
theorem optionalYulSemicolon_value_eq (value parsed : YulStmt)
    (input next : State)
    (result : optionalYulSemicolon value input = .ok parsed next) :
    parsed = value := by
  unfold optionalYulSemicolon getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon = true
  · simp only [present, if_true] at result
    cases semicolonResult : symbol .semicolon .yulStatement input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok marker afterMarker =>
        simp only [semicolonResult] at result
        cases result
        rfl
  · simp only [present, Bool.false_eq_true, if_false] at result
    cases result
    rfl

/-- Optional termination preserves recursive statement provenance. -/
theorem yulStatementTerminated_validFor (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (yulStatementTerminated nested).ValidFor YulStmt.ValidFor := by
  intro input inputValid
  unfold yulStatementTerminated
  cases coreResult : yulStatementCore nested input with
  | invariant error => simp [bind, coreResult, Reply.ValidFor]
  | reject failure rejected =>
      have valid := yulStatementCore_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [coreResult] at valid
      simpa only [bind, coreResult] using valid
  | ok value afterCore =>
      have valid := yulStatementCore_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [coreResult] at valid
      simpa only [bind, coreResult] using
        (optionalYulSemicolon_validForAt value afterCore valid.2.1
          (by simpa [valid.2.2] using valid.1)).of_file_eq valid.2.2

theorem yulStatementTerminated_preservesTokensOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (yulStatementTerminated nested) := by
  unfold yulStatementTerminated
  apply Parser.bind_preservesTokensOnSuccess
    (yulStatementCore_preservesTokensOnSuccess nested nestedValid
      nestedPreserves)
  intro value
  exact (optionalYulSemicolon_preservesTokenWindow value).preservesTokensOnSuccess

theorem yulStatementTerminated_cursorMonotoneOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulStatementTerminated nested) := by
  unfold yulStatementTerminated
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulStatementCore_cursorMonotoneOnSuccess nested nestedValid
      nestedPreserves)
  intro value
  exact optionalYulSemicolon_cursorMonotoneOnSuccess value

theorem yulStatementTerminated_startsAtCurrentTokenOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulStatementTerminated nested) (·.span) := by
  unfold yulStatementTerminated
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (yulStatementCore_startsAtCurrentTokenOnSuccess nested nestedValid
      nestedPreserves)
  intro value input parsed final result
  rw [optionalYulSemicolon_value_eq value parsed input final result]

private theorem yulStatementAdvance_state_shape {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

/-- Finishing statement recovery retains a source-valid error range. -/
theorem finishRecoveredYulStatement_validFor (first last : SourceSpan)
    (state : State) (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredYulStatement first last state).ValidFor state
      YulStmt.ValidFor := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredYulStatement Reply.ValidFor
  exact ⟨YulStmt.ValidFor.error spanValid,
    stateValid.emit_validFor _ spanValid, rfl⟩

/-- Statement recovery preserves the provenance of its consumed range. -/
theorem recoverYulStatementAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverYulStatementAux first last fuel state).ValidFor state
        YulStmt.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverYulStatementAux
      split
      · exact finishRecoveredYulStatement_validFor first last state
          stateValid firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredYulStatement_validFor first last state
              stateValid firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have nextValid := stateValid.advance?_validFor advanced
            have shape := yulStatementAdvance_state_shape advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            apply (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq
            simp [shape.2]

/-- Successful statement recovery preserves carrier, cursor, and first byte. -/
theorem recoverYulStatementAux_ok_state_shape (first : SourceSpan) :
    ∀ fuel last input statement next,
      recoverYulStatementAux first last fuel input = .ok statement next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        statement.span.startByte = first.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last input statement next result
      unfold recoverYulStatementAux at result
      split at result
      · unfold finishRecoveredYulStatement at result
        cases result
        exact ⟨rfl, Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredYulStatement at result
            cases result
            exact ⟨rfl, Nat.le_refl _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recursive := inductionHypothesis token.span afterToken
              statement next result
            have shape := yulStatementAdvance_state_shape advanced
            exact ⟨recursive.1.trans (by simp [shape.2]),
              Nat.le_trans (by simp [shape.2]) recursive.2.1,
              recursive.2.2⟩

/-- Statement recovery preserves every ordinary token window. -/
theorem recoverYulStatementAux_preservesTokenWindow (first last : SourceSpan) :
    ∀ fuel, Parser.PreservesTokenWindow
      (recoverYulStatementAux first last fuel) := by
  intro fuel input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverYulStatementAux
      split
      · unfold finishRecoveredYulStatement Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecoveredYulStatement Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            exact (inductionHypothesis token.span afterToken).trans (by
              simp [(yulStatementAdvance_state_shape advanced).2])

theorem recoverYulStatementAux_preservesTokensOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokensOnSuccess
      (recoverYulStatementAux first last fuel) :=
  (recoverYulStatementAux_preservesTokenWindow first last fuel).preservesTokensOnSuccess

theorem recoverYulStatementAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess
      (recoverYulStatementAux first last fuel) := by
  intro input statement next result
  exact (recoverYulStatementAux_ok_state_shape first fuel last input statement
    next result).2.1

/-- Optional termination retains any token-window contract of the core parser. -/
theorem yulStatementTerminated_preservesTokenWindow (nested : Parser YulStmt)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    Parser.PreservesTokenWindow (yulStatementTerminated nested) := by
  unfold yulStatementTerminated
  apply Parser.bind_preservesTokenWindow coreShape
  intro statement
  exact optionalYulSemicolon_preservesTokenWindow statement

/-- One recovering statement layer preserves recursive source provenance. -/
theorem yulStatementLayer_validFor (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    (yulStatementLayer nested).ValidFor YulStmt.ValidFor := by
  intro input inputValid
  unfold yulStatementLayer
  cases terminatedResult : yulStatementTerminated nested input with
  | ok statement next =>
      have valid := yulStatementTerminated_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [terminatedResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have terminatedValid := yulStatementTerminated_validFor nested nestedValid
        nestedPreserves input inputValid
      rw [terminatedResult] at terminatedValid
      have terminatedShape :=
        yulStatementTerminated_preservesTokenWindow nested coreShape input
      rw [terminatedResult] at terminatedShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := terminatedValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, terminatedShape.2] using
            inputValid.cursor_le_endIndex
        endIndex_le_size := terminatedValid.2.1.endIndex_le_size
        endByte_le_source := terminatedValid.2.1.endByte_le_source
        endByte_boundary := terminatedValid.2.1.endByte_boundary
        diagnosticsRev := terminatedValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using terminatedValid.2.2
      have failureValid : failure.span.ValidFor rewound.file := by
        simpa [rewound, terminatedValid.2.2] using terminatedValid.1
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, next) =>
            recoverYulStatementAux token.span token.span
              (next.remainingCount + 1) (next.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).ValidFor input YulStmt.ValidFor
      split
      · exact ⟨terminatedValid.1, rewoundValid, rewoundFile⟩
      · cases advanced : rewound.advance? with
        | none => exact ⟨terminatedValid.1, rewoundValid, rewoundFile⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            have advanceShape := yulStatementAdvance_state_shape advanced
            have nextValid := rewoundValid.advance?_validFor advanced
            have tokenValid : token.span.ValidFor next.file := by
              rw [advanceShape.2]
              exact rewoundValid.peek?_span_validFor advanceShape.1
            have emittedValid := nextValid.emit_validFor failure.toDiagnostic
              (by simpa [advanceShape.2] using
                failure.toDiagnostic_span_validFor failureValid)
            have currentFound :
                (next.emit failure.toDiagnostic).tokens[rewound.cursor]? =
                  some token := by
              simpa [advanceShape.2, State.emit] using
                State.getElem?_eq_some_of_peek?_eq_some advanceShape.1
            have recovered := recoverYulStatementAux_validFor token.span
              (next.remainingCount + 1) token.span
              (next.emit failure.toDiagnostic) rewound.cursor token emittedValid
              (by simpa [State.emit] using tokenValid)
              (by simpa [State.emit] using tokenValid)
              tokenValid.2.1 currentFound rfl (by
                simp [advanceShape.2, State.emit])
            exact recovered.of_file_eq (by
              simpa [advanceShape.2, State.emit] using rewoundFile)

/-- A recovering statement layer preserves every ordinary token window. -/
theorem yulStatementLayer_preservesTokenWindow (nested : Parser YulStmt)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    Parser.PreservesTokenWindow (yulStatementLayer nested) := by
  intro input
  unfold yulStatementLayer
  cases terminatedResult : yulStatementTerminated nested input with
  | invariant error => trivial
  | ok statement next =>
      have terminatedShape :=
        yulStatementTerminated_preservesTokenWindow nested coreShape input
      rw [terminatedResult] at terminatedShape
      exact terminatedShape
  | reject failure failedState =>
      have terminatedShape :=
        yulStatementTerminated_preservesTokenWindow nested coreShape input
      rw [terminatedResult] at terminatedShape
      let rewound : State := { failedState with cursor := input.cursor }
      have failedShape : failedState.tokens = input.tokens ∧
          failedState.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using terminatedShape
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := by
        simpa [rewound] using failedShape
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, next) =>
            recoverYulStatementAux token.span token.span
              (next.remainingCount + 1) (next.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound).PreservesTokenWindow input
      split
      · exact rewoundShape
      · cases advanced : rewound.advance? with
        | none => exact rewoundShape
        | some pair =>
            rcases pair with ⟨token, next⟩
            have recovered := recoverYulStatementAux_preservesTokenWindow
              token.span token.span (next.remainingCount + 1)
              (next.emit failure.toDiagnostic)
            have advanceShape := yulStatementAdvance_state_shape advanced
            exact recovered.trans (by
              simpa [State.emit, advanceShape.2] using rewoundShape)

theorem yulStatementLayer_preservesTokensOnSuccess (nested : Parser YulStmt)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    Parser.PreservesTokensOnSuccess (yulStatementLayer nested) :=
  (yulStatementLayer_preservesTokenWindow nested coreShape).preservesTokensOnSuccess

/-- A recovering statement layer never rewinds its caller's cursor. -/
theorem yulStatementLayer_cursorMonotoneOnSuccess (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (yulStatementLayer nested) := by
  intro input statement next result
  unfold yulStatementLayer at result
  cases terminatedResult : yulStatementTerminated nested input with
  | invariant error => simp [terminatedResult] at result
  | ok value afterCore =>
      simp only [terminatedResult] at result
      have monotone := yulStatementTerminated_cursorMonotoneOnSuccess nested
        nestedValid nestedPreserves input value afterCore terminatedResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [terminatedResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverYulStatementAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok statement next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have recovered := recoverYulStatementAux_cursorMonotoneOnSuccess
              token.span token.span (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic) statement next result
            have advanceShape := yulStatementAdvance_state_shape advanced
            exact Nat.le_trans (by simp [advanceShape.2, State.emit, rewound])
              recovered

/-- A successful recovering layer starts at its caller's current token. -/
theorem yulStatementLayer_startsAtCurrentTokenOnSuccess
    (nested : Parser YulStmt)
    (nestedValid : nested.ValidFor YulStmt.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (coreShape : Parser.PreservesTokenWindow (yulStatementCore nested)) :
    Parser.StartsAtCurrentTokenOnSuccess (yulStatementLayer nested) (·.span) := by
  intro input statement next result
  unfold yulStatementLayer at result
  cases terminatedResult : yulStatementTerminated nested input with
  | invariant error => simp [terminatedResult] at result
  | ok value afterCore =>
      simp only [terminatedResult] at result
      have starts := yulStatementTerminated_startsAtCurrentTokenOnSuccess nested
        nestedValid nestedPreserves input value afterCore terminatedResult
      cases result
      simpa using starts
  | reject failure failedState =>
      simp only [terminatedResult] at result
      have terminatedShape :=
        yulStatementTerminated_preservesTokenWindow nested coreShape input
      rw [terminatedResult] at terminatedShape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
        Reply.reject failure rewound else
        match rewound.advance? with
        | some (token, afterToken) =>
            recoverYulStatementAux token.span token.span
              (afterToken.remainingCount + 1)
              (afterToken.emit failure.toDiagnostic)
        | none => Reply.reject failure rewound) = .ok statement next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have advanceShape := yulStatementAdvance_state_shape advanced
            have found : input.peek? = some token := by
              have rewoundFound := advanceShape.1
              unfold State.peek? at rewoundFound ⊢
              simpa [rewound, terminatedShape.1, terminatedShape.2] using
                rewoundFound
            have recovered := recoverYulStatementAux_ok_state_shape token.span
              (afterToken.remainingCount + 1) token.span
              (afterToken.emit failure.toDiagnostic) statement next result
            exact ⟨token, found, recovered.2.2.symm⟩

/-- Every fuel-bounded statement parser preserves ordinary token windows. -/
theorem yulStatementWithFuel_preservesTokenWindow :
    ∀ fuel, Parser.PreservesTokenWindow (yulStatementWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero => intro input; trivial
  | succ fuel inductionHypothesis =>
      exact yulStatementLayer_preservesTokenWindow
        (yulStatementWithFuel fuel)
        (yulStatementCore_preservesTokenWindow
          (yulStatementWithFuel fuel) inductionHypothesis)

theorem yulStatementWithFuel_preservesTokensOnSuccess (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (yulStatementWithFuel fuel) :=
  (yulStatementWithFuel_preservesTokenWindow fuel).preservesTokensOnSuccess

/-- Every fuel-bounded statement parser retains source provenance. -/
theorem yulStatementWithFuel_validFor :
    ∀ fuel, (yulStatementWithFuel fuel).ValidFor YulStmt.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intro input inputValid; trivial
  | succ fuel inductionHypothesis =>
      have nestedShape := yulStatementWithFuel_preservesTokenWindow fuel
      exact yulStatementLayer_validFor (yulStatementWithFuel fuel)
        inductionHypothesis nestedShape.preservesTokensOnSuccess
        (yulStatementCore_preservesTokenWindow
          (yulStatementWithFuel fuel) nestedShape)

/-- Fuel-bounded statement successes never rewind their caller. -/
theorem yulStatementWithFuel_cursorMonotoneOnSuccess :
    ∀ fuel, Parser.CursorMonotoneOnSuccess (yulStatementWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input statement next result
      simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      have nestedShape := yulStatementWithFuel_preservesTokenWindow fuel
      exact yulStatementLayer_cursorMonotoneOnSuccess
        (yulStatementWithFuel fuel)
        (yulStatementWithFuel_validFor fuel)
        nestedShape.preservesTokensOnSuccess

/-- Fuel-bounded statement successes begin at the current token. -/
theorem yulStatementWithFuel_startsAtCurrentTokenOnSuccess :
    ∀ fuel, Parser.StartsAtCurrentTokenOnSuccess
      (yulStatementWithFuel fuel) (·.span) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input statement next result
      simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      have nestedShape := yulStatementWithFuel_preservesTokenWindow fuel
      exact yulStatementLayer_startsAtCurrentTokenOnSuccess
        (yulStatementWithFuel fuel)
        (yulStatementWithFuel_validFor fuel)
        nestedShape.preservesTokensOnSuccess
        (yulStatementCore_preservesTokenWindow
          (yulStatementWithFuel fuel) nestedShape)

/-- Public Yul statement parsing preserves every ordinary token window. -/
theorem yulStatement_preservesTokenWindow :
    Parser.PreservesTokenWindow yulStatement := by
  intro input
  unfold yulStatement
  exact yulStatementWithFuel_preservesTokenWindow
    (input.remainingCount + 1) input

theorem yulStatement_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulStatement :=
  yulStatement_preservesTokenWindow.preservesTokensOnSuccess

/-- Public Yul statement parsing retains source provenance. -/
theorem yulStatement_validFor : yulStatement.ValidFor YulStmt.ValidFor := by
  intro input inputValid
  unfold yulStatement
  exact yulStatementWithFuel_validFor (input.remainingCount + 1)
    input inputValid

/-- Public Yul statement successes never rewind their caller. -/
theorem yulStatement_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulStatement := by
  intro input statement next result
  unfold yulStatement at result
  exact yulStatementWithFuel_cursorMonotoneOnSuccess
    (input.remainingCount + 1) input statement next result

/-- Public Yul statement successes begin at the current token. -/
theorem yulStatement_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulStatement (·.span) := by
  intro input statement next result
  unfold yulStatement at result
  exact yulStatementWithFuel_startsAtCurrentTokenOnSuccess
    (input.remainingCount + 1) input statement next result

/-- A complete Yul body retains every statement and its enclosing range. -/
theorem yulBody_validFor :
    yulBody.ValidFor (YulParsedBlock.ValidFor YulStmt.ValidFor) :=
  yulBlock_validFor YulStmt.ValidFor yulStatement yulStatement_validFor
    yulStatement_preservesTokensOnSuccess

/-- Complete Yul bodies preserve every ordinary token window. -/
theorem yulBody_preservesTokenWindow :
    Parser.PreservesTokenWindow yulBody :=
  yulBlock_preservesTokenWindow yulStatement
    yulStatement_preservesTokenWindow

theorem yulBody_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess yulBody :=
  yulBody_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful Yul-body parsing never rewinds its caller. -/
theorem yulBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess yulBody :=
  yulBlock_cursorMonotoneOnSuccess yulStatement
    yulStatement_preservesTokensOnSuccess

/-- A successful Yul body starts at its opening brace token. -/
theorem yulBody_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess yulBody (·.span) :=
  yulBlock_startsAtCurrentTokenOnSuccess yulStatement
    yulStatement_preservesTokensOnSuccess

end Solcore.Syntax.Parser
