import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent grammar for raw braced Core statement sequences.

This layer describes direct block recognition inside one active token window.
It does not include the parser's balanced-block isolation wrapper.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Whether the final expression statement of a Core block needs a semicolon. -/
inductive CoreBlockTailPolicy where
  | allow
  | require
  deriving Repr, BEq, DecidableEq

/-- A statement is acceptable where an expression semicolon is mandatory. -/
def CoreBlockStatementTerminated (statement : Syntax.Statement) : Prop :=
  match statement.value with
  | .expression _ false => False
  | _ => True

/--
Exact diagnostic-free condition imposed by Core block-tail validation.

Every non-final expression statement must retain a semicolon.  The final
statement has the same requirement under `require`, while `allow` accepts it
unchanged.  Empty blocks and every non-expression statement are accepted.
-/
def CoreBlockTailsValid :
    CoreBlockTailPolicy → List Syntax.Statement → Prop
  | _, [] => True
  | .allow, [_] => True
  | .require, [last] => CoreBlockStatementTerminated last
  | policy, first :: second :: rest =>
      CoreBlockStatementTerminated first ∧
        CoreBlockTailsValid policy (second :: rest)

@[simp] theorem coreBlockTailsValid_nil (policy : CoreBlockTailPolicy) :
    CoreBlockTailsValid policy [] := by
  simp [CoreBlockTailsValid]

@[simp] theorem coreBlockTailsValid_allow_singleton
    (statement : Syntax.Statement) :
    CoreBlockTailsValid .allow [statement] := by
  simp [CoreBlockTailsValid]

@[simp] theorem coreBlockTailsValid_require_singleton
    (statement : Syntax.Statement) :
    CoreBlockTailsValid .require [statement] =
      CoreBlockStatementTerminated statement := by
  simp [CoreBlockTailsValid]

@[simp] theorem coreBlockTailsValid_cons_cons
    (policy : CoreBlockTailPolicy) (first second : Syntax.Statement)
    (rest : List Syntax.Statement) :
    CoreBlockTailsValid policy (first :: second :: rest) =
      (CoreBlockStatementTerminated first ∧
        CoreBlockTailsValid policy (second :: rest)) := by
  simp [CoreBlockTailsValid]

/--
Forward-order Core statements followed by their exact closing brace.

The recursive branch records that the preferred right-brace branch did not
match.  Its strict progress premise mirrors the executable loop's successful
statement guard independently of that loop's fuel bound.
-/
inductive CoreBlockItemsParses
    (statementParses :
      Remainder → Syntax.Statement → Remainder → Prop) :
    Remainder → List Syntax.Statement → SourceSpan →
      Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingToken : ExactTokenParses (.symbol .rightBrace)
        input closingSpan output) :
      CoreBlockItemsParses statementParses input [] closingSpan output
  | next {input afterStatement output : Remainder}
      {statement : Syntax.Statement} {statements : List Syntax.Statement}
      {closingSpan : SourceSpan}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementParses input statement afterStatement)
      (progress : input.cursor < afterStatement.cursor)
      (tail : CoreBlockItemsParses statementParses afterStatement statements
        closingSpan output) :
      CoreBlockItemsParses statementParses input (statement :: statements)
        closingSpan output

/-- A block-items derivation consumes at least its closing brace. -/
theorem CoreBlockItemsParses.cursor_lt
    {statementParses :
      Remainder → Syntax.Statement → Remainder → Prop}
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan}
    (parsed : CoreBlockItemsParses statementParses input statements
      closingSpan output) :
    input.cursor < output.cursor := by
  induction parsed with
  | close closingSpan closingToken =>
      rcases closingToken with ⟨_, rfl⟩
      simp
  | next notAtEnd closingAbsent statementParsed progress tail
      inductionHypothesis =>
      exact Nat.lt_trans progress inductionHypothesis

/--
Block items preserve their active token window whenever the abstract statement
judgment does.
-/
theorem CoreBlockItemsParses.output_window
    {statementParses :
      Remainder → Syntax.Statement → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statements : List Syntax.Statement}
    {closingSpan : SourceSpan}
    (parsed : CoreBlockItemsParses statementParses input statements
      closingSpan output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close closingSpan closingToken =>
      rcases closingToken with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩
  | next notAtEnd closingAbsent statementParsed progress tail
      inductionHypothesis =>
      have step := statementWindow statementParsed
      exact ⟨inductionHypothesis.1.trans step.1,
        inductionHypothesis.2.trans step.2⟩

/-- Exact braces, covering span, source-order body, and tail policy of a block. -/
inductive CoreBlockParses
    (statementParses :
      Remainder → Syntax.Statement → Remainder → Prop)
    (policy : CoreBlockTailPolicy) :
    Remainder → Syntax.Block → Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {body : List Syntax.Statement} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace)
        input openingSpan afterOpening)
      (bodyParsed : CoreBlockItemsParses statementParses afterOpening body
        closingSpan output)
      (tailsValid : CoreBlockTailsValid policy body) :
      CoreBlockParses statementParses policy input {
        span := SourceSpan.cover openingSpan closingSpan
        value := body
      } output

/-- Every raw Core block derivation makes strict cursor progress. -/
theorem CoreBlockParses.cursor_lt
    {statementParses :
      Remainder → Syntax.Statement → Remainder → Prop}
    {policy : CoreBlockTailPolicy} {input output : Remainder}
    {block : Syntax.Block}
    (parsed : CoreBlockParses statementParses policy input block output) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed openingSpan closingSpan openingToken bodyParsed tailsValid =>
      rcases openingToken with ⟨_, rfl⟩
      exact Nat.lt_trans (by simp) bodyParsed.cursor_lt

/--
A raw Core block preserves its active window whenever its statement judgment
does.
-/
theorem CoreBlockParses.output_window
    {statementParses :
      Remainder → Syntax.Statement → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {policy : CoreBlockTailPolicy} {input output : Remainder}
    {block : Syntax.Block}
    (parsed : CoreBlockParses statementParses policy input block output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed openingSpan closingSpan openingToken bodyParsed tailsValid =>
      rcases openingToken with ⟨_, rfl⟩
      exact bodyParsed.output_window statementWindow

end Solcore.Syntax.DeclarativeGrammar
