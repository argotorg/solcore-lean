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

/--
Yul `for` parsing preserves every statement in its initializer, post block,
and body together with the loop condition.  The recursive statement parser
and fixed expression parser remain explicit dependencies.
-/
theorem yulForStatement_validFor (statement : Parser YulStmt)
    (expressionValid : yulExpression.ValidFor YulExpr.ValidFor)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    (yulForStatement statement).ValidFor YulStmt.ValidFor := by
  have weak : (yulForStatement statement).ValidFor (fun _ _ => True) := by
    unfold yulForStatement
    apply Parser.bind_validFor (keyword_validFor .forKw .yulStatement)
    intro marker
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro initializer
    apply Parser.bind_validFor expressionValid
    intro condition
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro post
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulForStatement statement input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulForStatement at stages
      rcases yulBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨initializer, afterInitializer, initializerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨condition, afterCondition, conditionResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨post, afterPost, postResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := keyword_validFor .forKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      have initializerValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterMarker markerValid.2.1
      rw [initializerResult] at initializerValid
      have conditionValid := expressionValid afterInitializer
        initializerValid.2.1
      rw [conditionResult] at conditionValid
      have postValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterCondition conditionValid.2.1
      rw [postResult] at postValid
      have bodyValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterPost postValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have initializerStatementsValid :
          ∀ retained ∈ initializer.body,
            YulStmt.ValidFor input.file retained := by
        intro retained member
        simpa [markerValid.2.2] using initializerValid.1.2 retained member
      have conditionValidInput : YulExpr.ValidFor input.file condition := by
        simpa [initializerValid.2.2, markerValid.2.2] using
          conditionValid.1
      have postStatementsValid :
          ∀ retained ∈ post.body, YulStmt.ValidFor input.file retained := by
        intro retained member
        simpa [conditionValid.2.2, initializerValid.2.2,
          markerValid.2.2] using postValid.1.2 retained member
      have bodySpanValid : body.span.ValidFor input.file := by
        simpa [postValid.2.2, conditionValid.2.2,
          initializerValid.2.2, markerValid.2.2] using bodyValid.1.1
      have bodyStatementsValid :
          ∀ retained ∈ body.body, YulStmt.ValidFor input.file retained := by
        intro retained member
        simpa [postValid.2.2, conditionValid.2.2,
          initializerValid.2.2, markerValid.2.2] using
          bodyValid.1.2 retained member
      have markerShape := acceptToken_ok_state_shape
        (.keyword .forKw) .yulStatement (· == .keyword .forKw) markerResult
      have markerAt :=
        State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      rcases yulBlock_startsAtCurrentTokenOnSuccess statement
          statementPreserves afterPost body afterBody bodyResult with
        ⟨openingToken, openingFound, openingStart⟩
      have openingAtInput :
          input.tokens[afterPost.cursor]? = some openingToken := by
        have openingAt :=
          State.getElem?_eq_some_of_peek?_eq_some openingFound
        have postTokens := yulBlock_preservesTokensOnSuccess statement
          statementPreserves afterCondition post afterPost postResult
        have conditionTokens := expressionPreserves afterInitializer condition
          afterCondition conditionResult
        have initializerTokens := yulBlock_preservesTokensOnSuccess statement
          statementPreserves afterMarker initializer afterInitializer
          initializerResult
        have markerTokens := keyword_preservesTokensOnSuccess .forKw
          .yulStatement input marker afterMarker markerResult
        simpa [postTokens, conditionTokens, initializerTokens, markerTokens]
          using openingAt
      have initializerProgress := yulBlock_cursor_lt_onSuccess statement
        statementPreserves initializerResult
      have conditionCursor := expressionMonotone afterInitializer condition
        afterCondition conditionResult
      have postProgress := yulBlock_cursor_lt_onSuccess statement
        statementPreserves postResult
      have initializerAfterMarker :
          input.cursor + 1 < afterInitializer.cursor := by
        simpa [markerShape.2] using initializerProgress
      have markerBeforeOpening : input.cursor < afterPost.cursor := by
        omega
      have markerBeforeBody : marker.span.endByte ≤ body.span.startByte := by
        rw [← openingStart]
        exact inputValid.token_end_le_token_start_of_getElem?_lt markerAt
          openingAtInput markerBeforeOpening
      have outerValid :
          (SourceSpan.cover marker.span body.span).ValidFor input.file := by
        apply SourceSpan.cover_validFor markerSpanValid bodySpanValid
        exact Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeBody bodySpanValid.2.1)
      cases finished
      exact ⟨YulStmt.ValidFor.forLoop outerValid initializerStatementsValid
          conditionValidInput postStatementsValid bodyStatementsValid,
        weakResult.2.1, weakResult.2.2⟩

/-- Yul `for` parsing preserves the immutable lexer token carrier. -/
theorem yulForStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (expressionPreserves :
      Parser.PreservesTokensOnSuccess yulExpression)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulForStatement statement) := by
  unfold yulForStatement
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .forKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro initializer
  apply Parser.bind_preservesTokensOnSuccess expressionPreserves
  intro condition
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro post
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_preservesTokensOnSuccess _

/-- Yul `for` parsing never moves the parser cursor backwards. -/
theorem yulForStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (expressionMonotone :
      Parser.CursorMonotoneOnSuccess yulExpression)
    (statementPreserves :
      Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulForStatement statement) := by
  unfold yulForStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .forKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess expressionMonotone
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro post
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A successful Yul `for` statement starts at its current `for` token. -/
theorem yulForStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulForStatement statement) (·.span) := by
  unfold yulForStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .forKw) .yulStatement (· == .keyword .forKw))
  intro marker input value final parsed
  rcases yulBind_ok_components parsed with
    ⟨initializer, afterInitializer, _initializerResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨condition, afterCondition, _conditionResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨post, afterPost, _postResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

private theorem yulReturnClause_validFor :
    YulControl.returnClause.ValidFor YulReturnClause.ValidFor := by
  have weak : YulControl.returnClause.ValidFor (fun _ _ => True) := by
    unfold YulControl.returnClause
    apply Parser.bind_validFor (symbol_validFor .arrow .yulStatement)
    intro arrow
    apply Parser.bind_validFor yulNames_validFor
    intro names
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : YulControl.returnClause input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weakResult; exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold YulControl.returnClause at stages
      rcases yulBind_ok_components stages with
        ⟨arrow, afterArrow, arrowResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨names, afterNames, namesResult, finished⟩
      have arrowValid := symbol_validFor .arrow .yulStatement input inputValid
      rw [arrowResult] at arrowValid
      have namesValid := yulNames_validFor afterArrow arrowValid.2.1
      rw [namesResult] at namesValid
      have arrowSpanValid : arrow.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using arrowValid.1
      have namesSpanValid : names.span.ValidFor input.file := by
        simpa [arrowValid.2.2] using namesValid.1.1
      have arrowShape := symbol_ok_state_shape .arrow .yulStatement arrowResult
      have arrowAdvanced : input.advance? = some (arrow, afterArrow) := by
        unfold State.advance?
        rw [arrowShape.1, arrowShape.2]
        rfl
      rcases yulNames_startsAtCurrentTokenOnSuccess afterArrow names
          afterNames namesResult with ⟨first, firstFound, firstStart⟩
      have arrowBeforeNames : arrow.span.startByte ≤ names.span.endByte :=
        Nat.le_trans arrowSpanValid.2.1 (Nat.le_trans
          (by
            rw [← firstStart]
            exact inputValid.consumed_end_le_peek_start_after_advance
              arrowAdvanced firstFound)
          namesSpanValid.2.1)
      cases finished
      refine ⟨⟨SourceSpan.cover_validFor arrowSpanValid namesSpanValid
          arrowBeforeNames, arrowSpanValid, ?_⟩,
        weakResult.2.1, weakResult.2.2⟩
      intro name member
      simpa [arrowValid.2.2] using namesValid.1.2 name member
theorem yulReturns_validFor : YulControl.returns.ValidFor
      (Option.ValidFor YulReturnClause.ValidFor) := by
  unfold YulControl.returns
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value yulReturnClause_validFor
    intro clause input inputValid clauseValid
    exact ⟨by simpa only [Option.ValidFor] using clauseValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none
      (Option.ValidFor YulReturnClause.ValidFor) (fun _ => trivial)
private theorem yulReturnClause_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess YulControl.returnClause := by
  unfold YulControl.returnClause
  apply Parser.bind_preservesTokensOnSuccess
    (symbol_preservesTokensOnSuccess .arrow .yulStatement)
  intro arrow
  apply Parser.bind_preservesTokensOnSuccess
    yulNames_preservesTokensOnSuccess
  intro names
  exact Parser.pure_preservesTokensOnSuccess _
theorem yulReturns_preservesTokensOnSuccess : Parser.PreservesTokensOnSuccess YulControl.returns := by
  unfold YulControl.returns
  apply Parser.bind_preservesTokensOnSuccess getState_preservesTokensOnSuccess
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_preservesTokensOnSuccess
      yulReturnClause_preservesTokensOnSuccess
    intro clause
    exact Parser.pure_preservesTokensOnSuccess _
  · simp only [present]
    exact Parser.pure_preservesTokensOnSuccess none
private theorem yulReturnClause_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess YulControl.returnClause := by
  unfold YulControl.returnClause
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .arrow .yulStatement)
  intro arrow
  apply Parser.bind_cursorMonotoneOnSuccess
    yulNames_cursorMonotoneOnSuccess
  intro names
  exact Parser.pure_cursorMonotoneOnSuccess _
theorem yulReturns_cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess YulControl.returns := by
  unfold YulControl.returns
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .arrow
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      yulReturnClause_cursorMonotoneOnSuccess
    intro clause
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none
/-- Yul function definitions retain every name, delimiter, and body range. -/
theorem yulFunctionStatement_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (yulFunctionStatement statement).ValidFor YulStmt.ValidFor := by
  have weak : (yulFunctionStatement statement).ValidFor
      (fun _ _ => True) := by
    unfold yulFunctionStatement
    apply Parser.bind_validFor (keyword_validFor .functionKw .yulStatement)
    intro marker
    apply Parser.bind_validFor yulName_validFor
    intro name
    apply Parser.bind_validFor yulParameters_validFor
    intro parameters
    apply Parser.bind_validFor yulReturns_validFor
    intro returns
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : yulFunctionStatement statement input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weakResult; exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold yulFunctionStatement at stages
      rcases yulBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨parameters, afterParameters, parametersResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨returns, afterReturns, returnsResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := keyword_validFor .functionKw .yulStatement
        input inputValid
      rw [markerResult] at markerValid
      have nameValid := yulName_validFor afterMarker markerValid.2.1
      rw [nameResult] at nameValid
      have parametersValid := yulParameters_validFor afterName nameValid.2.1
      rw [parametersResult] at parametersValid
      have returnsValid := yulReturns_validFor afterParameters
        parametersValid.2.1
      rw [returnsResult] at returnsValid
      have bodyValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterReturns returnsValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have bodySpanValid : body.span.ValidFor input.file := by
        simpa [returnsValid.2.2, parametersValid.2.2, nameValid.2.2,
          markerValid.2.2] using bodyValid.1.1
      have markerShape := acceptToken_ok_state_shape
        (.keyword .functionKw) .yulStatement
        (· == .keyword .functionKw) markerResult
      have markerAt :=
        State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      rcases yulBlock_startsAtCurrentTokenOnSuccess statement
          statementPreserves afterReturns body afterBody bodyResult with
        ⟨opening, openingFound, openingStart⟩
      have openingAtInput : input.tokens[afterReturns.cursor]? = some opening := by
        have openingAt := State.getElem?_eq_some_of_peek?_eq_some openingFound
        simpa [yulReturns_preservesTokensOnSuccess afterParameters returns
          afterReturns returnsResult,
          yulParameters_preservesTokensOnSuccess afterName parameters
            afterParameters parametersResult,
          yulName_preservesTokensOnSuccess afterMarker name afterName nameResult,
          keyword_preservesTokensOnSuccess .functionKw .yulStatement input
            marker afterMarker markerResult] using openingAt
      have nameCursor := yulName_cursorMonotoneOnSuccess afterMarker name
        afterName nameResult
      have parametersCursor := yulParameters_cursorMonotoneOnSuccess afterName
        parameters afterParameters parametersResult
      have returnsCursor := yulReturns_cursorMonotoneOnSuccess afterParameters
        returns afterReturns returnsResult
      have markerBeforeOpening : input.cursor < afterReturns.cursor := by
        have afterMarkerBefore : input.cursor + 1 ≤ afterReturns.cursor := by
          simpa [markerShape.2] using
            Nat.le_trans nameCursor (Nat.le_trans parametersCursor returnsCursor)
        omega
      have markerBeforeBody : marker.span.endByte ≤ body.span.startByte := by
        rw [← openingStart]
        exact inputValid.token_end_le_token_start_of_getElem?_lt markerAt
          openingAtInput markerBeforeOpening
      have outerValid := SourceSpan.cover_validFor markerSpanValid bodySpanValid
        (Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeBody bodySpanValid.2.1))
      cases finished
      exact ⟨YulStmt.ValidFor.functionDef outerValid
          (by simpa only [Located.ValidFor, markerValid.2.2] using nameValid.1)
          (by simpa only [DelimitedList.ValidFor, Located.ValidFor,
            nameValid.2.2, markerValid.2.2] using parametersValid.1)
          (by simpa [parametersValid.2.2, nameValid.2.2,
            markerValid.2.2] using returnsValid.1)
          (by
            intro retained member
            simpa [returnsValid.2.2, parametersValid.2.2, nameValid.2.2,
            markerValid.2.2] using bodyValid.1.2 retained member),
        weakResult.2.1, weakResult.2.2⟩
/-- Yul function parsing preserves the immutable lexer token carrier. -/
theorem yulFunctionStatement_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (yulFunctionStatement statement) := by
  unfold yulFunctionStatement
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .functionKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess yulName_preservesTokensOnSuccess
  intro name
  apply Parser.bind_preservesTokensOnSuccess
    yulParameters_preservesTokensOnSuccess
  intro parameters
  apply Parser.bind_preservesTokensOnSuccess yulReturns_preservesTokensOnSuccess
  intro returns
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_preservesTokensOnSuccess _
/-- Yul function parsing never rewinds the parser cursor. -/
theorem yulFunctionStatement_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (yulFunctionStatement statement) := by
  unfold yulFunctionStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .functionKw .yulStatement)
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
/-- A successful Yul function definition starts at its `function` token. -/
theorem yulFunctionStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (yulFunctionStatement statement) (·.span) := by
  unfold yulFunctionStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .functionKw) .yulStatement (· == .keyword .functionKw))
  intro marker input value final parsed
  rcases yulBind_ok_components parsed with ⟨name, afterName, _, rest⟩
  rcases yulBind_ok_components rest with ⟨parameters, afterParameters, _, rest⟩
  rcases yulBind_ok_components rest with ⟨returns, afterReturns, _, rest⟩
  rcases yulBind_ok_components rest with ⟨body, afterBody, _, finished⟩
  cases finished
  rfl

/-- One Yul switch arm retains its literal, body, and outer source ranges. -/
theorem yulCase_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (YulControl.caseArm statement).ValidFor YulCase.ValidFor := by
  have weak : (YulControl.caseArm statement).ValidFor
      (fun _ _ => True) := by
    unfold YulControl.caseArm
    apply Parser.bind_validFor (keyword_validFor .caseKw .yulStatement)
    intro marker
    apply Parser.bind_validFor yulLiteral_validFor
    intro literal
    apply Parser.bind_validFor
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : YulControl.caseArm statement input with
  | invariant error => trivial
  | reject failure rejected => rw [parsed] at weakResult; exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold YulControl.caseArm at stages
      rcases yulBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨literal, afterLiteral, literalResult, rest⟩
      rcases yulBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := keyword_validFor .caseKw .yulStatement input inputValid
      rw [markerResult] at markerValid
      have literalValid := yulLiteral_validFor afterMarker markerValid.2.1
      rw [literalResult] at literalValid
      have bodyValid := yulBlock_validFor YulStmt.ValidFor statement
        statementValid statementPreserves afterLiteral literalValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have bodySpanValid : body.span.ValidFor input.file := by
        simpa [literalValid.2.2, markerValid.2.2] using bodyValid.1.1
      have markerShape := acceptToken_ok_state_shape
        (.keyword .caseKw) .yulStatement (· == .keyword .caseKw) markerResult
      have markerAt :=
        State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      rcases yulBlock_startsAtCurrentTokenOnSuccess statement
          statementPreserves afterLiteral body afterBody bodyResult with
        ⟨opening, openingFound, openingStart⟩
      have openingAtInput : input.tokens[afterLiteral.cursor]? = some opening := by
        have openingAt := State.getElem?_eq_some_of_peek?_eq_some openingFound
        simpa [yulLiteral_preservesTokensOnSuccess afterMarker literal
          afterLiteral literalResult,
          keyword_preservesTokensOnSuccess .caseKw .yulStatement input marker
            afterMarker markerResult] using openingAt
      have literalCursor := yulLiteral_cursorMonotoneOnSuccess afterMarker
        literal afterLiteral literalResult
      have markerBeforeOpening : input.cursor < afterLiteral.cursor := by
        have afterMarkerBefore : input.cursor + 1 ≤ afterLiteral.cursor := by
          simpa [markerShape.2] using literalCursor
        omega
      have markerBeforeBody : marker.span.endByte ≤ body.span.startByte := by
        rw [← openingStart]
        exact inputValid.token_end_le_token_start_of_getElem?_lt markerAt
          openingAtInput markerBeforeOpening
      have outerValid := SourceSpan.cover_validFor markerSpanValid bodySpanValid
        (Nat.le_trans markerSpanValid.2.1
          (Nat.le_trans markerBeforeBody bodySpanValid.2.1))
      cases finished
      exact ⟨YulCase.ValidFor.arm outerValid
          (by simpa [Located.ValidFor, markerValid.2.2] using literalValid.1)
          (by
            intro retained member
            simpa [literalValid.2.2, markerValid.2.2] using
              bodyValid.1.2 retained member),
        weakResult.2.1, weakResult.2.2⟩

/-- Yul switch-arm parsing preserves the immutable lexer token carrier. -/
theorem yulCase_preservesTokensOnSuccess (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (YulControl.caseArm statement) := by
  unfold YulControl.caseArm
  apply Parser.bind_preservesTokensOnSuccess
    (keyword_preservesTokensOnSuccess .caseKw .yulStatement)
  intro marker
  apply Parser.bind_preservesTokensOnSuccess yulLiteral_preservesTokensOnSuccess
  intro literal
  apply Parser.bind_preservesTokensOnSuccess
    (yulBlock_preservesTokensOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_preservesTokensOnSuccess _

/-- Yul switch-arm parsing never rewinds the parser cursor. -/
theorem yulCase_cursorMonotoneOnSuccess (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess (YulControl.caseArm statement) := by
  unfold YulControl.caseArm
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .caseKw .yulStatement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess yulLiteral_cursorMonotoneOnSuccess
  intro literal
  apply Parser.bind_cursorMonotoneOnSuccess
    (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Repeated Yul switch arms retain the nested parser's token carrier. -/
theorem yulCases_preservesTokensOnSuccess (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    ∀ fuel casesRev, Parser.PreservesTokensOnSuccess
      (YulControl.caseList statement fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input value next result
      unfold YulControl.caseList at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro casesRev input value next result
      unfold YulControl.caseList at result
      split at result
      · cases armResult : YulControl.caseArm statement input with
        | ok arm afterArm =>
            simp only [armResult] at result
            split at result
            · exact (inductionHypothesis (arm :: casesRev) afterArm value next
                result).trans
                (yulCase_preservesTokensOnSuccess statement statementPreserves
                  input arm afterArm armResult)
            · contradiction
        | reject failure rejected => simp [armResult] at result
        | invariant error => simp [armResult] at result
      · cases result
        rfl

/-- Repeated Yul switch arms never rewind the parser cursor. -/
theorem yulCases_cursorMonotoneOnSuccess (statement : Parser YulStmt) :
    ∀ fuel casesRev, Parser.CursorMonotoneOnSuccess
      (YulControl.caseList statement fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input value next result
      unfold YulControl.caseList at result
      contradiction
  | succ fuel inductionHypothesis =>
      intro casesRev input value next result
      unfold YulControl.caseList at result
      split at result
      · cases armResult : YulControl.caseArm statement input with
        | ok arm afterArm =>
            simp only [armResult] at result
            split at result
            · exact Nat.le_trans (Nat.le_of_lt (by assumption))
                (inductionHypothesis (arm :: casesRev) afterArm value next
                  result)
            · contradiction
        | reject failure rejected => simp [armResult] at result
        | invariant error => simp [armResult] at result
      · cases result
        exact Nat.le_refl _

private theorem yulCases_validFor_aux (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    ∀ fuel casesRev input,
      input.ValidFor →
      List.ValidFor YulCase.ValidFor input.file casesRev →
      (YulControl.caseList statement fuel casesRev input).ValidFor input
        (List.ValidFor YulCase.ValidFor) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro casesRev input inputValid casesValid
      unfold YulControl.caseList
      split
      · cases armResult : YulControl.caseArm statement input with
        | invariant error => trivial
        | reject failure rejected =>
            have valid := yulCase_validFor statement statementValid
              statementPreserves input inputValid
            rw [armResult] at valid
            exact valid
        | ok arm afterArm =>
            have armValid := yulCase_validFor statement statementValid
              statementPreserves input inputValid
            rw [armResult] at armValid
            simp only
            split
            · apply (inductionHypothesis (arm :: casesRev) afterArm
                  armValid.2.1 ?_).of_file_eq armValid.2.2
              intro retained member
              rcases List.mem_cons.mp member with rfl | member
              · simpa [armValid.2.2] using armValid.1
              · simpa [armValid.2.2] using casesValid retained member
            · trivial
      · exact ⟨by
            intro arm member
            exact casesValid arm (by simpa using member),
          inputValid, rfl⟩

/-- Repeated Yul switch arms preserve every recursively retained range. -/
theorem yulCases_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    (fuel : Nat) :
    Parser.ValidFor (YulControl.caseList statement fuel [])
      (List.ValidFor YulCase.ValidFor) := by
  intro input inputValid
  exact yulCases_validFor_aux statement statementValid statementPreserves
    fuel [] input inputValid (by simp [List.ValidFor])

private theorem yulCase_starts_aux (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (YulControl.caseArm statement) (·.span) := by
  unfold YulControl.caseArm
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .caseKw) .yulStatement (· == .keyword .caseKw))
  intro marker input value final parsed
  rcases yulBind_ok_components parsed with ⟨literal, afterLiteral, _, rest⟩
  rcases yulBind_ok_components rest with ⟨body, afterBody, _, finished⟩
  cases finished
  rfl

/-- Every accumulated switch arm begins after a supplied consumed token. -/
theorem yulCases_ordered_after (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    ∀ fuel casesRev input output next anchorIndex anchor,
      input.ValidFor →
      input.tokens[anchorIndex]? = some anchor →
      anchorIndex < input.cursor →
      (∀ arm ∈ casesRev,
        anchor.span.endByte ≤ arm.span.startByte) →
      YulControl.caseList statement fuel casesRev input = .ok output next →
      ∀ arm ∈ output, anchor.span.endByte ≤ arm.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro casesRev input output next anchorIndex anchor inputValid
        anchorFound anchorBeforeCursor casesOrdered result
      unfold YulControl.caseList at result
      split at result
      · cases armResult : YulControl.caseArm statement input with
        | ok arm afterArm =>
            simp only [armResult] at result
            have armValid := yulCase_validFor statement statementValid
              statementPreserves input inputValid
            rw [armResult] at armValid
            split at result
            · rcases yulCase_starts_aux statement input arm
                  afterArm armResult with ⟨marker, markerFound, armStart⟩
              apply inductionHypothesis (arm :: casesRev) afterArm output next
                anchorIndex anchor armValid.2.1
              · simpa [yulCase_preservesTokensOnSuccess statement
                    statementPreserves input arm afterArm armResult] using
                  anchorFound
              · omega
              · intro retained member
                rcases List.mem_cons.mp member with rfl | member
                · rw [← armStart]
                  exact inputValid.token_end_le_token_start_of_getElem?_lt
                    anchorFound
                    (State.getElem?_eq_some_of_peek?_eq_some markerFound)
                    anchorBeforeCursor
                · exact casesOrdered retained member
              · exact result
            · contradiction
        | reject failure rejected => simp [armResult] at result
        | invariant error => simp [armResult] at result
      · intro arm member
        cases result
        exact casesOrdered arm (by simpa using member)

/-- A present default block begins after every earlier consumed token. -/
theorem optionalYulDefault_some_ordered_after
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : YulParsedBlock}
    {anchorIndex : Nat} {anchor : Token}
    (inputValid : input.ValidFor)
    (anchorFound : input.tokens[anchorIndex]? = some anchor)
    (anchorBeforeCursor : anchorIndex < input.cursor)
    (result : YulControl.optionalDefault statement input = .ok (some body) next) :
    anchor.span.endByte ≤ body.span.startByte := by
  unfold YulControl.optionalDefault getState at result
  simp only [bind] at result
  by_cases present : isKeyword input .defaultKw
  · simp only [present, if_true] at result
    rcases yulBind_ok_components result with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases yulBind_ok_components rest with
      ⟨parsedBody, afterBody, bodyResult, finished⟩
    have bodyStarts := yulBlock_startsAtCurrentTokenOnSuccess statement
      statementPreserves afterMarker parsedBody afterBody bodyResult
    cases finished
    rcases bodyStarts with
      ⟨opening, openingFound, openingStart⟩
    rw [← openingStart]
    apply inputValid.token_end_le_token_start_of_getElem?_lt anchorFound
    · simpa [keyword_preservesTokensOnSuccess .defaultKw .yulStatement
          input marker afterMarker markerResult] using
        State.getElem?_eq_some_of_peek?_eq_some openingFound
    · have shape := acceptToken_ok_state_shape
          (.keyword .defaultKw) .yulStatement
          (· == .keyword .defaultKw) markerResult
      simpa [shape.2] using
        Nat.lt_trans anchorBeforeCursor (Nat.lt_succ_self input.cursor)
  · simp only [present, Bool.false_eq_true, if_false] at result
    cases result

/-- A successful Yul switch arm starts at its current `case` token. -/
theorem yulCase_startsAtCurrentTokenOnSuccess (statement : Parser YulStmt) :
    Parser.StartsAtCurrentTokenOnSuccess
      (YulControl.caseArm statement) (·.span) :=
  yulCase_starts_aux statement

/-- A successful Yul switch arm consumes its marker, literal, and block. -/
theorem yulCase_cursor_lt_onSuccess (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {arm : YulCase}
    (result : YulControl.caseArm statement input = .ok arm next) :
    input.cursor < next.cursor := by
  have stages := result
  unfold YulControl.caseArm at stages
  rcases yulBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨literal, afterLiteral, literalResult, rest⟩
  rcases yulBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  have markerShape := acceptToken_ok_state_shape
    (.keyword .caseKw) .yulStatement (· == .keyword .caseKw) markerResult
  have literalCursor := yulLiteral_cursorMonotoneOnSuccess afterMarker literal
    afterLiteral literalResult
  have bodyProgress := yulBlock_cursor_lt_onSuccess statement
    statementPreserves bodyResult
  cases finished
  simp [markerShape.2] at literalCursor
  omega

/-- Optional Yul defaults preserve their block and statement provenance. -/
theorem optionalYulDefault_validFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor YulStmt.ValidFor)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    (YulControl.optionalDefault statement).ValidFor
      (Option.ValidFor (YulParsedBlock.ValidFor YulStmt.ValidFor)) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_validFor (keyword_validFor .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_validFor_of_value
      (yulBlock_validFor YulStmt.ValidFor statement statementValid
        statementPreserves)
    intro body input inputValid bodyValid
    exact ⟨by simpa only [Option.ValidFor] using bodyValid, inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional Yul defaults preserve the immutable lexer token carrier. -/
theorem optionalYulDefault_preservesTokensOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess
      (YulControl.optionalDefault statement) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_preservesTokensOnSuccess getState_preservesTokensOnSuccess
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_preservesTokensOnSuccess
      (keyword_preservesTokensOnSuccess .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_preservesTokensOnSuccess
      (yulBlock_preservesTokensOnSuccess statement statementPreserves)
    intro body
    exact Parser.pure_preservesTokensOnSuccess _
  · simp only [present]
    exact Parser.pure_preservesTokensOnSuccess none

/-- Optional Yul defaults never rewind the parser cursor. -/
theorem optionalYulDefault_cursorMonotoneOnSuccess
    (statement : Parser YulStmt)
    (statementPreserves : Parser.PreservesTokensOnSuccess statement) :
    Parser.CursorMonotoneOnSuccess
      (YulControl.optionalDefault statement) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed .defaultKw
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (yulBlock_cursorMonotoneOnSuccess statement statementPreserves)
    intro body
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none


end Solcore.Syntax.Parser
