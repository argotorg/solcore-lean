import Solcore.Syntax.Parser.Statement.Control
import Solcore.Syntax.StatementValidity

/-! Contracts for canonical Core control-statement parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem controlBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
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

/-- A braced statement wrapper retains the block range and every body item. -/
theorem blockStatement_validFor
    (statement : Parser Statement)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement) :
    (blockStatement statement).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  unfold blockStatement
  apply Parser.bind_validFor_of_value
    (coreBlock_validFor
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      statement .require statementValid statementTokens
      (fun _ _ valid => valid.span_valid))
  intro body next nextValid bodyValid
  exact ⟨Statement.ValidFor.block bodyValid.1 bodyValid.2, nextValid, rfl⟩

/-- Braced statement wrappers preserve the complete token window. -/
theorem blockStatement_preservesTokenWindow
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (blockStatement statement) := by
  unfold blockStatement
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Braced statement wrappers retain the immutable token carrier on success. -/
theorem blockStatement_preservesTokensOnSuccess
    (statement : Parser Statement)
    (statementWindow : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokensOnSuccess (blockStatement statement) :=
  (blockStatement_preservesTokenWindow statement
    statementWindow).preservesTokensOnSuccess

/-- A braced statement wrapper never rewinds the token cursor. -/
theorem blockStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) :
    Parser.CursorMonotoneOnSuccess (blockStatement statement) := by
  unfold blockStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A braced statement wrapper starts at its opening brace. -/
theorem blockStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) :
    Parser.StartsAtCurrentTokenOnSuccess
      (blockStatement statement) (·.span) := by
  unfold blockStatement
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (coreBlock_startsAtCurrentTokenOnSuccess statement .require)
  intro body input wrapped final parsed
  cases parsed
  rfl

/-- A successful `while` statement retains a valid keyword-to-body range. -/
theorem whileStatement_span_validOnSuccess
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionTokens : Parser.PreservesTokensOnSuccess expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {parsedStatement : Statement}
    (inputValid : input.ValidFor)
    (parsed : whileStatement statement expression input =
      .ok parsedStatement final) :
    parsedStatement.span.ValidFor input.file := by
  have stages := parsed
  unfold whileStatement at stages
  rcases controlBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨condition, afterCondition, conditionResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  have markerReply := contextual_validFor .while .statement input inputValid
  rw [markerResult] at markerReply
  have openingReply := symbol_validFor .leftParen .statement afterMarker
    markerReply.2.1
  rw [openingResult] at openingReply
  have conditionReply := expressionValid afterOpening openingReply.2.1
  rw [conditionResult] at conditionReply
  have closingReply := symbol_validFor .rightParen .statement afterCondition
    conditionReply.2.1
  rw [closingResult] at closingReply
  have bodyParserValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  have bodyReply := bodyParserValid afterClosing closingReply.2.1
  rw [bodyResult] at bodyReply
  have markerValid : marker.span.ValidFor input.file := by
    simpa only [Located.ValidFor] using markerReply.1
  have bodyValid : Block.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      input.file body := by
    simpa [bodyReply.2.2, closingReply.2.2, conditionReply.2.2,
      openingReply.2.2, markerReply.2.2] using bodyReply.1
  rcases coreBlock_startsAtCurrentTokenOnSuccess statement .require
      afterClosing body afterBody bodyResult with
    ⟨bodyOpening, bodyOpeningFound, bodyStart⟩
  have markerAt := State.getElem?_eq_some_of_peek?_eq_some
    (acceptToken_ok_state_shape (.contextual .while) .statement
      (·.isContextual .while) markerResult).1
  have bodyOpeningAtAfter :=
    State.getElem?_eq_some_of_peek?_eq_some bodyOpeningFound
  have bodyOpeningAt : input.tokens[afterClosing.cursor]? =
      some bodyOpening := by
    simpa [
      contextual_preservesTokensOnSuccess .while .statement input marker
        afterMarker markerResult,
      symbol_preservesTokensOnSuccess .leftParen .statement afterMarker
        opening afterOpening openingResult,
      expressionTokens afterOpening condition afterCondition conditionResult,
      symbol_preservesTokensOnSuccess .rightParen .statement afterCondition
        closing afterClosing closingResult] using bodyOpeningAtAfter
  have cursorOrder : input.cursor < afterClosing.cursor :=
    Nat.lt_of_lt_of_le
      (acceptToken_cursor_lt_onSuccess (.contextual .while) .statement
        (·.isContextual .while) markerResult)
      (Nat.le_trans
        (symbol_cursorMonotoneOnSuccess .leftParen .statement afterMarker
          opening afterOpening openingResult)
        (Nat.le_trans
          (expressionCursor afterOpening condition afterCondition
            conditionResult)
          (symbol_cursorMonotoneOnSuccess .rightParen .statement
            afterCondition closing afterClosing closingResult)))
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt
    markerAt bodyOpeningAt cursorOrder
  have ordered : marker.span.startByte ≤ body.span.endByte := by
    calc
      marker.span.startByte ≤ marker.span.endByte := markerValid.2.1
      _ ≤ bodyOpening.span.startByte := separated
      _ = body.span.startByte := bodyStart
      _ ≤ body.span.endByte := bodyValid.1.2.1
  cases finished
  exact SourceSpan.cover_validFor markerValid bodyValid.1 ordered

/-- `while` parsing retains its condition, body, and complete outer range. -/
theorem whileStatement_validFor
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementValid : statement.ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid))
    (statementTokens : Parser.PreservesTokensOnSuccess statement)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionTokens : Parser.PreservesTokensOnSuccess expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    (whileStatement statement expression).ValidFor
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) := by
  have bodyValid := coreBlock_validFor
    (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
    statement .require statementValid statementTokens
    (fun _ _ valid => valid.span_valid)
  have weak : (whileStatement statement expression).ValidFor
      (fun _ _ => True) := by
    unfold whileStatement
    apply Parser.bind_validFor (contextual_validFor .while .statement)
    intro marker
    apply Parser.bind_validFor (symbol_validFor .leftParen .statement)
    intro opening
    apply Parser.bind_validFor expressionValid
    intro condition
    apply Parser.bind_validFor (symbol_validFor .rightParen .statement)
    intro closing
    apply Parser.bind_validFor bodyValid
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakReply := weak input inputValid
  cases parsed : whileStatement statement expression input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakReply
      exact weakReply
  | ok parsedStatement final =>
      rw [parsed] at weakReply
      have stages := parsed
      unfold whileStatement at stages
      rcases controlBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨opening, afterOpening, openingResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨condition, afterCondition, conditionResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨closing, afterClosing, closingResult, rest⟩
      rcases controlBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerReply := contextual_validFor .while .statement input
        inputValid
      rw [markerResult] at markerReply
      have openingReply := symbol_validFor .leftParen .statement afterMarker
        markerReply.2.1
      rw [openingResult] at openingReply
      have conditionReply := expressionValid afterOpening openingReply.2.1
      rw [conditionResult] at conditionReply
      have closingReply := symbol_validFor .rightParen .statement
        afterCondition conditionReply.2.1
      rw [closingResult] at closingReply
      have bodyReply := bodyValid afterClosing closingReply.2.1
      rw [bodyResult] at bodyReply
      have conditionValidInput : expressionValueValid input.file condition := by
        simpa [conditionReply.2.2, openingReply.2.2,
          markerReply.2.2] using conditionReply.1
      have bodyValidInput : Block.ValidFor
          (Statement.ValidFor expressionValueValid patternValueValid
            yulValueValid) input.file body := by
        simpa [bodyReply.2.2, closingReply.2.2, conditionReply.2.2,
          openingReply.2.2, markerReply.2.2] using bodyReply.1
      have outerValid := whileStatement_span_validOnSuccess
        expressionValueValid patternValueValid yulValueValid statement
          expression statementValid statementTokens expressionValid
          expressionTokens expressionCursor inputValid parsed
      cases finished
      exact ⟨Statement.ValidFor.whileLoop outerValid conditionValidInput
        bodyValidInput.1 bodyValidInput.2, weakReply.2.1,
        weakReply.2.2⟩

/-- `while` parsing preserves every ordinary token window. -/
theorem whileStatement_preservesTokenWindow
    (statement : Parser Statement) (expression : Parser Expr)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokenWindow (whileStatement statement expression) := by
  unfold whileStatement
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .while .statement)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .leftParen .statement)
  intro opening
  apply Parser.bind_preservesTokenWindow expressionWindow
  intro condition
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightParen .statement)
  intro closing
  apply Parser.bind_preservesTokenWindow
    (coreBlock_preservesTokenWindow statement .require statementWindow)
  intro body
  exact Parser.pure_preservesTokenWindow _

/-- Successful `while` parsing preserves the immutable token carrier. -/
theorem whileStatement_preservesTokensOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (statementWindow : Parser.PreservesTokenWindow statement)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    Parser.PreservesTokensOnSuccess (whileStatement statement expression) :=
  (whileStatement_preservesTokenWindow statement expression statementWindow
    expressionWindow).preservesTokensOnSuccess

/-- A successful `while` statement never rewinds the token cursor. -/
theorem whileStatement_cursorMonotoneOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression) :
    Parser.CursorMonotoneOnSuccess (whileStatement statement expression) := by
  unfold whileStatement
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .while .statement)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .leftParen .statement)
  intro opening
  apply Parser.bind_cursorMonotoneOnSuccess expressionCursor
  intro condition
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightParen .statement)
  intro closing
  apply Parser.bind_cursorMonotoneOnSuccess
    (coreBlock_cursorMonotoneOnSuccess statement .require)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A `while` statement starts at its contextual keyword token. -/
theorem whileStatement_startsAtCurrentTokenOnSuccess
    (statement : Parser Statement) (expression : Parser Expr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (whileStatement statement expression) (·.span) := by
  intro input parsedStatement final parsed
  have stages := parsed
  unfold whileStatement at stages
  rcases controlBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨condition, afterCondition, conditionResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  rcases controlBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  rcases contextual_startsAtCurrentTokenOnSuccess .while .statement input
      marker afterMarker markerResult with ⟨token, found, starts⟩
  cases finished
  exact ⟨token, found, starts⟩

end Solcore.Syntax.Parser
