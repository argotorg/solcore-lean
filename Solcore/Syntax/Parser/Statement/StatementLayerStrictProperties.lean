import Solcore.Syntax.Parser.Statement.StatementLayerFuelTotalityProperties

/-! Strict cursor progress for the complete ordered Core statement dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

private theorem bind_cursor_lt_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input middle : State} {value : alpha},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [bind, firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [bind, firstResult] at parsed
  | invariant error => simp [bind, firstResult] at parsed

private theorem assignmentOrExpression_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionStrict : ∀ {input final : State} {value : Expr},
      expression input = .ok value final → input.cursor < final.cursor)
    {input final : State} {value : Statement}
    (parsed : assignmentOrExpressionStatement expression input =
      .ok value final) :
    input.cursor < final.cursor := by
  let expressionCursor : Parser.CursorMonotoneOnSuccess expression :=
    fun _ _ _ result => Nat.le_of_lt (expressionStrict result)
  unfold assignmentOrExpressionStatement at parsed
  apply bind_cursor_lt_of_first expressionStrict ?_ parsed
  intro left
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalAssignmentTail_cursorMonotoneOnSuccess
      expression expressionCursor)
  intro tail
  apply Parser.bind_cursorMonotoneOnSuccess
    StatementSimpleInternals.optionalSemicolon_cursorMonotoneOnSuccess
  intro semicolon
  dsimp only
  cases tail with
  | none => exact Parser.pure_cursorMonotoneOnSuccess _
  | some tail =>
      cases tail <;> by_cases missing : semicolon.isNone
      · simp only [missing, if_true]
        apply Parser.bind_cursorMonotoneOnSuccess
          (emitDiagnostic_cursorMonotoneOnSuccess _)
        intro _
        exact Parser.pure_cursorMonotoneOnSuccess _
      · simp only [missing, Bool.false_eq_true, ↓reduceIte]
        exact Parser.pure_cursorMonotoneOnSuccess _
      · simp only [missing, if_true]
        apply Parser.bind_cursorMonotoneOnSuccess
          (emitDiagnostic_cursorMonotoneOnSuccess _)
        intro _
        exact Parser.pure_cursorMonotoneOnSuccess _
      · simp only [missing, Bool.false_eq_true, ↓reduceIte]
        exact Parser.pure_cursorMonotoneOnSuccess _

private theorem let_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : letStatement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold letStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .letKw)
      .statement (· == .keyword .letKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .statement); intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    StatementSimpleInternals.optionalLetType_cursorMonotoneOnSuccess; intro type
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalLetInitializer_cursorMonotoneOnSuccess
      expression expressionCursor); intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem return_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : returnStatement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold returnStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .returnKw)
      .statement (· == .keyword .returnKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (StatementSimpleInternals.optionalReturnValue_cursorMonotoneOnSuccess
      expression expressionCursor); intro value
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem for_cursor_lt_onSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : forStatement statement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold forStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .forKw)
      .statement (· == .keyword .forKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement); intro opening
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.forItems_cursorMonotoneOnSuccess expression .semicolon
      expressionCursor); intro initializer
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor; intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.forItems_cursorMonotoneOnSuccess expression .rightParen
      expressionCursor); intro post
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement); intro closing
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require); intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem while_cursor_lt_onSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : whileStatement statement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold whileStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.contextual .while)
      .statement (·.isContextual .while) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor; intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require); intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem if_cursor_lt_onSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : Statement}
    (parsed : ifStatement statement expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold ifStatement at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .ifKw)
      .statement (· == .keyword .ifKw) result) ?_ parsed
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor; intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement); intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require); intro thenBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (ControlInternals.optionalElseBody_cursorMonotoneOnSuccess statement)
  intro elseBody
  exact Parser.pure_cursorMonotoneOnSuccess _

private theorem block_cursor_lt_onSuccess
    (statement : Parser Statement) {input final : State} {value : Statement}
    (parsed : blockStatement statement input = .ok value final) :
    input.cursor < final.cursor := by
  unfold blockStatement at parsed
  apply bind_cursor_lt_of_first (coreBlock_cursor_lt_onSuccess statement
    .require) (fun body => Parser.pure_cursorMonotoneOnSuccess _) parsed

/-- Every successful ordered Core statement branch consumes a token. -/
theorem statementLayer_cursor_lt_onSuccess
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (expressionStrict : ∀ {input final : State} {value : Expr},
      expression input = .ok value final → input.cursor < final.cursor)
    {input final : State} {value : Statement}
    (parsed : statementLayer nestedStatement expression pattern input =
      .ok value final) :
    input.cursor < final.cursor := by
  let expressionCursor : Parser.CursorMonotoneOnSuccess expression :=
    fun _ _ _ result => Nat.le_of_lt (expressionStrict result)
  have fallbackStrict : ∀ {start stop : State} {statement : Statement},
      assignmentOrExpressionStatement expression start = .ok statement stop →
        start.cursor < stop.cursor :=
    assignmentOrExpression_cursor_lt_onSuccess expression expressionStrict
  unfold statementLayer at parsed
  dsimp only at parsed
  split at parsed
  · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
      _ _ (let_cursor_lt_onSuccess expression expressionCursor)
        fallbackStrict parsed
  · split at parsed
    · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
        _ _ (return_cursor_lt_onSuccess expression expressionCursor)
          fallbackStrict parsed
    · split at parsed
      · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
          _ _ (matchStatement_cursor_lt_onSuccess nestedStatement expression
            pattern) fallbackStrict parsed
      · split at parsed
        · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
            _ _ (for_cursor_lt_onSuccess nestedStatement expression
              expressionCursor) fallbackStrict parsed
        · split at parsed
          · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
              _ _ (while_cursor_lt_onSuccess nestedStatement expression
                expressionCursor) fallbackStrict parsed
          · split at parsed
            · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                _ _ (if_cursor_lt_onSuccess nestedStatement expression
                  expressionCursor) fallbackStrict parsed
            · split at parsed
              · exact recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                  _ _ assemblyStatement_cursor_lt_onSuccess fallbackStrict
                    parsed
              · split at parsed
                · exact
                    recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                      _ _ (block_cursor_lt_onSuccess nestedStatement)
                        fallbackStrict parsed
                · split at parsed
                  · exact
                      recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                        _ _ breakStatement_cursor_lt_onSuccess fallbackStrict
                          parsed
                  · split at parsed
                    · exact
                        recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
                          _ _ continueStatement_cursor_lt_onSuccess
                            fallbackStrict parsed
                    · exact fallbackStrict parsed

end Solcore.Syntax.Parser.TermInternals
