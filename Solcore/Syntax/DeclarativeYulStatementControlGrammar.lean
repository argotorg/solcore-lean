import Solcore.Syntax.DeclarativeYulBlockGrammar

/-!
Parser-independent grammar for Yul block, `if`, and `for` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lift one exact braced Yul block into statement position. -/
inductive YulBlockStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input output : Remainder} {bodySpan : SourceSpan}
      {body : List Syntax.YulStmt}
      (bodyParsed : YulBlockParses statementParses input bodySpan body
        output) :
      YulBlockStatementParses statementParses input {
        span := bodySpan
        value := .block body
      } output

/-- Exact keyword, condition, block, span, and AST of a Yul `if`. -/
inductive YulIfStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterCondition output : Remainder}
      {condition : Syntax.YulExpr} {bodySpan : SourceSpan}
      {body : List Syntax.YulStmt} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (conditionParsed : expressionParses afterMarker condition
        afterCondition)
      (bodyParsed : YulBlockParses statementParses afterCondition bodySpan
        body output) :
      YulIfStatementParses statementParses expressionParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .ifThen condition body
      } output

/-- Exact source-order blocks, condition, spans, and AST of a Yul `for`. -/
inductive YulForStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterInitializer afterCondition afterPost
        output : Remainder}
      {initializerSpan postSpan bodySpan : SourceSpan}
      {initializer post body : List Syntax.YulStmt}
      {condition : Syntax.YulExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerParsed : YulBlockParses statementParses afterMarker
        initializerSpan initializer afterInitializer)
      (conditionParsed : expressionParses afterInitializer condition
        afterCondition)
      (postParsed : YulBlockParses statementParses afterCondition postSpan
        post afterPost)
      (bodyParsed : YulBlockParses statementParses afterPost bodySpan body
        output) :
      YulForStatementParses statementParses expressionParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .forLoop initializer condition post body
      } output

theorem YulBlockStatementParses.cursor_lt
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulBlockStatementParses statementParses input statement output) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed bodyParsed => exact bodyParsed.cursor_lt

theorem YulBlockStatementParses.output_window
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulBlockStatementParses statementParses input statement output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed bodyParsed => exact bodyParsed.output_window statementWindow

theorem YulIfStatementParses.cursor_lt
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    (expressionCursor : ∀ {input expression output},
      expressionParses input expression output →
        input.cursor ≤ output.cursor)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulIfStatementParses statementParses expressionParses input
      statement output) : input.cursor < output.cursor := by
  cases parsed with
  | parsed markerSpan markerParsed conditionParsed bodyParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      exact Nat.lt_trans (by simp)
        (Nat.lt_of_le_of_lt (expressionCursor conditionParsed)
          bodyParsed.cursor_lt)

theorem YulIfStatementParses.output_window
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    (expressionWindow : ∀ {input expression output},
      expressionParses input expression output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulIfStatementParses statementParses expressionParses input
      statement output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed markerSpan markerParsed conditionParsed bodyParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      have conditionWindow := expressionWindow conditionParsed
      have blockWindow := bodyParsed.output_window statementWindow
      exact ⟨blockWindow.1.trans conditionWindow.1,
        blockWindow.2.trans conditionWindow.2⟩

theorem YulForStatementParses.cursor_lt
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    (expressionCursor : ∀ {input expression output},
      expressionParses input expression output →
        input.cursor ≤ output.cursor)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulForStatementParses statementParses expressionParses input
      statement output) : input.cursor < output.cursor := by
  cases parsed with
  | parsed markerSpan markerParsed initializerParsed conditionParsed
      postParsed bodyParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      have markerProgress : input.cursor <
          ({ input with cursor := input.cursor + 1 } : Remainder).cursor := by
        simp
      have throughInitializer := Nat.lt_trans markerProgress
        initializerParsed.cursor_lt
      have throughCondition := Nat.lt_of_lt_of_le throughInitializer
        (expressionCursor conditionParsed)
      exact Nat.lt_trans (Nat.lt_trans throughCondition postParsed.cursor_lt)
        bodyParsed.cursor_lt

theorem YulForStatementParses.output_window
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    (expressionWindow : ∀ {input expression output},
      expressionParses input expression output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulForStatementParses statementParses expressionParses input
      statement output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed markerSpan markerParsed initializerParsed conditionParsed
      postParsed bodyParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      have initializerWindow := initializerParsed.output_window statementWindow
      have conditionWindow := expressionWindow conditionParsed
      have postWindow := postParsed.output_window statementWindow
      have bodyWindow := bodyParsed.output_window statementWindow
      exact ⟨bodyWindow.1.trans (postWindow.1.trans
          (conditionWindow.1.trans initializerWindow.1)),
        bodyWindow.2.trans (postWindow.2.trans
          (conditionWindow.2.trans initializerWindow.2))⟩

end Solcore.Syntax.DeclarativeGrammar
