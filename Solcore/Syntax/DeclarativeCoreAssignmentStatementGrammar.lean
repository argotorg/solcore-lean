import Solcore.Syntax.DeclarativeCoreStatementSimpleGrammar

/-!
Parser-independent grammar for Core assignment and expression statements.

The grammar retains the parser's `~=` priority, maximal optional assignment
tail, optional semicolon, exact source spans, and the diagnostic-free rule that
every assignment has a semicolon.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Parser-independent payload of an assignment suffix. -/
inductive CoreAssignmentTail where
  | value (operator : Located ValueAssignOp) (right : Expr)
  | bitNot (operator : SourceSpan)
  deriving Repr, BEq

/-- Exact tokens of one value-assignment operator: one token, or the two
adjacent tokens of `<<=` and `>>=`, as `ValueAssignOp.at?` decodes them. -/
def ValueAssignOperatorParses (input : Remainder)
    (operator : Located ValueAssignOp) (output : Remainder) : Prop :=
  ValueAssignOp.at? input.tokens input.endIndex input.cursor = some operator ∧
    output = { input with cursor := input.cursor + operator.value.tokenCount }

/-- No value-assignment operator occurs at the current cursor. -/
def ValueAssignOperatorAbsentAt (input : Remainder) : Prop :=
  ValueAssignOp.at? input.tokens input.endIndex input.cursor = none

namespace ValueAssignOperatorParses

/-- The decoded operator fixes its span, its value and the remainder. -/
theorem unique {input leftOutput rightOutput : Remainder}
    {left right : Located ValueAssignOp}
    (leftParsed : ValueAssignOperatorParses input left leftOutput)
    (rightParsed : ValueAssignOperatorParses input right rightOutput) :
    left = right ∧ leftOutput = rightOutput := by
  have same : left = right := Option.some.inj (leftParsed.1.symm.trans rightParsed.1)
  subst same
  exact ⟨rfl, leftParsed.2.trans rightParsed.2.symm⟩

/-- A decoded operator excludes absence. -/
theorem not_absent {input output : Remainder} {operator : Located ValueAssignOp}
    (parsed : ValueAssignOperatorParses input operator output)
    (absent : ValueAssignOperatorAbsentAt input) : False := by
  unfold ValueAssignOperatorAbsentAt at absent
  rw [parsed.1] at absent
  contradiction

end ValueAssignOperatorParses

/-- Neither assignment-tail form starts at the current cursor. -/
def AssignmentTailAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .tildeEqual) ∧
    ValueAssignOperatorAbsentAt input

/-- Exact prioritized grammar for one assignment suffix. -/
inductive AssignmentTailParses
    (expressionParses : Remainder → Expr → Remainder → Prop) :
    Remainder → CoreAssignmentTail → Remainder → Prop where
  | bitNot {input output : Remainder} (operatorSpan : SourceSpan)
      (operatorParsed : ExactTokenParses (.symbol .tildeEqual) input
        operatorSpan output) :
      AssignmentTailParses expressionParses input (.bitNot operatorSpan)
        output
  | value {input afterOperator output : Remainder}
      {operator : Located ValueAssignOp} {right : Expr}
      (tildeEqualAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .tildeEqual))
      (operatorParsed : ValueAssignOperatorParses input operator afterOperator)
      (rightParsed : expressionParses afterOperator right output) :
      AssignmentTailParses expressionParses input (.value operator right)
        output

/-- Maximal optional assignment suffix. -/
inductive OptionalAssignmentTailParses
    (expressionParses : Remainder → Expr → Remainder → Prop) :
    Remainder → Option CoreAssignmentTail → Remainder → Prop where
  | absent {input : Remainder} (tailAbsent : AssignmentTailAbsentAt input) :
      OptionalAssignmentTailParses expressionParses input none input
  | present {input output : Remainder} {tail : CoreAssignmentTail}
      (tailParsed : AssignmentTailParses expressionParses input tail output) :
      OptionalAssignmentTailParses expressionParses input (some tail) output

/-- Pure final span of one assignment suffix. -/
def assignmentEnd : CoreAssignmentTail → SourceSpan
  | .value _ right => right.span
  | .bitNot operator => operator

/-- Pure final span selected before constructing the covering statement span. -/
def statementEnd (left : Expr) (tail : Option CoreAssignmentTail)
    (semicolon : Option SourceSpan) : SourceSpan :=
  match semicolon, tail with
  | some marker, _ => marker
  | none, some value => assignmentEnd value
  | none, none => left.span

/--
Diagnostic-free construction of the statement payload.  Assignment cases
intentionally require `some semicolon`; the executable missing-semicolon
success emits a diagnostic and therefore has no constructor here.
-/
inductive AssignmentOrExpressionBuilds :
    Expr → Option CoreAssignmentTail → Option SourceSpan → Statement → Prop
    where
  | expression (left : Expr) (semicolon : Option SourceSpan) :
      AssignmentOrExpressionBuilds left none semicolon {
        span := SourceSpan.cover left.span (statementEnd left none semicolon)
        value := .expression left semicolon.isSome
      }
  | value (left right : Expr) (operator : Located ValueAssignOp)
      (semicolon : SourceSpan) :
      AssignmentOrExpressionBuilds left (some (.value operator right))
        (some semicolon) {
          span := SourceSpan.cover left.span
            (statementEnd left (some (.value operator right)) (some semicolon))
          value := .assignValue left operator right
        }
  | bitNot (left : Expr) (operator semicolon : SourceSpan) :
      AssignmentOrExpressionBuilds left (some (.bitNot operator))
        (some semicolon) {
          span := SourceSpan.cover left.span
            (statementEnd left (some (.bitNot operator)) (some semicolon))
          value := .assignBitNot left operator
        }

/-- Exact diagnostic-free Core assignment-or-expression statement grammar. -/
def AssignmentOrExpressionStatementParses
    (expressionParses : Remainder → Expr → Remainder → Prop)
    (input : Remainder) (statement : Statement) (output : Remainder) : Prop :=
  ∃ left afterLeft tail afterTail semicolon,
    expressionParses input left afterLeft ∧
      OptionalAssignmentTailParses expressionParses afterLeft tail afterTail ∧
      OptionalStatementSemicolonParses afterTail semicolon output ∧
      AssignmentOrExpressionBuilds left tail semicolon statement

end Solcore.Syntax.DeclarativeGrammar
