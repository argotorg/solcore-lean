import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent grammar for braced Yul statement blocks.

The item grammar retains right-brace priority, excludes the missing-close
at-end path, requires strict statement progress, and returns statements in
source order.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact closing brace and covering span for an accumulated Yul block body. -/
inductive CloseYulBlockParses (openingSpan : SourceSpan)
    (body : List Syntax.YulStmt) :
    Remainder → SourceSpan → Remainder → Prop where
  | parsed {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace) input
        closingSpan output) :
      CloseYulBlockParses openingSpan body input
        (SourceSpan.cover openingSpan closingSpan) output

/--
Forward-order Yul statements followed by their exact closing brace.  The
recursive branch records both preferred-close absence and non-end-of-window.
-/
inductive YulBlockItemsParses
    (statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (openingSpan : SourceSpan) :
    Remainder → SourceSpan → List Syntax.YulStmt → Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace) input
        closingSpan output) :
      YulBlockItemsParses statementParses openingSpan input
        (SourceSpan.cover openingSpan closingSpan) [] output
  | next {input afterStatement output : Remainder}
      {bodySpan : SourceSpan} {statement : Syntax.YulStmt}
      {statements : List Syntax.YulStmt}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementParses input statement afterStatement)
      (progress : input.cursor < afterStatement.cursor)
      (tail : YulBlockItemsParses statementParses openingSpan afterStatement
        bodySpan statements output) :
      YulBlockItemsParses statementParses openingSpan input bodySpan
        (statement :: statements) output

/-- Exact opening brace, block span, forward body, and final remainder. -/
inductive YulBlockParses
    (statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → SourceSpan → List Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {bodySpan : SourceSpan} {body : List Syntax.YulStmt}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) input
        openingSpan afterOpening)
      (bodyParsed : YulBlockItemsParses statementParses openingSpan
        afterOpening bodySpan body output) :
      YulBlockParses statementParses input bodySpan body output

theorem CloseYulBlockParses.cursor_lt
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : CloseYulBlockParses openingSpan body input bodySpan output) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed closingSpan closingParsed =>
      rcases closingParsed with ⟨_, rfl⟩
      simp

theorem CloseYulBlockParses.output_window
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : CloseYulBlockParses openingSpan body input bodySpan output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed closingSpan closingParsed =>
      rcases closingParsed with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩

theorem YulBlockItemsParses.cursor_lt
    {statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : YulBlockItemsParses statementParses openingSpan input bodySpan
      body output) : input.cursor < output.cursor := by
  induction parsed with
  | close closingSpan closingParsed =>
      rcases closingParsed with ⟨_, rfl⟩
      simp
  | next notAtEnd closingAbsent statementParsed progress tail
      inductionHypothesis =>
      exact Nat.lt_trans progress inductionHypothesis

theorem YulBlockItemsParses.output_window
    {statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : YulBlockItemsParses statementParses openingSpan input bodySpan
      body output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close closingSpan closingParsed =>
      rcases closingParsed with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩
  | next notAtEnd closingAbsent statementParsed progress tail
      inductionHypothesis =>
      have step := statementWindow statementParsed
      exact ⟨inductionHypothesis.1.trans step.1,
        inductionHypothesis.2.trans step.2⟩

theorem YulBlockParses.cursor_lt
    {statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output : Remainder} {bodySpan : SourceSpan}
    {body : List Syntax.YulStmt}
    (parsed : YulBlockParses statementParses input bodySpan body output) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed openingSpan openingParsed bodyParsed =>
      rcases openingParsed with ⟨_, rfl⟩
      exact Nat.lt_trans (by simp) bodyParsed.cursor_lt

theorem YulBlockParses.output_window
    {statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {bodySpan : SourceSpan}
    {body : List Syntax.YulStmt}
    (parsed : YulBlockParses statementParses input bodySpan body output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed openingSpan openingParsed bodyParsed =>
      rcases openingParsed with ⟨_, rfl⟩
      exact bodyParsed.output_window statementWindow

end Solcore.Syntax.DeclarativeGrammar
