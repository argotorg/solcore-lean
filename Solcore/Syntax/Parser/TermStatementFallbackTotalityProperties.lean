import Solcore.Syntax.Parser.ExpressionProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties
import Solcore.Syntax.Parser.TermStatementTotalityProperties

/-! Valid-input totality for the terminal Core-statement fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace StatementSimpleInternals

/-- The custom value-assignment operator parser has no invariant branch. -/
theorem valueAssignOperator_invariantFreeOnValid :
    Parser.InvariantFreeOnValid valueAssignOperator := by
  intro input _inputValid
  cases result : valueAssignOperator input with
  | ok operator next => exact Or.inl ⟨operator, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold valueAssignOperator at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          simp only [found] at result
          cases accepted : valueAssignOp? token.value with
          | none => simp [accepted, rejectAt] at result
          | some operator => simp [accepted] at result

/-- Assignment suffixes inherit valid-input totality from expressions. -/
theorem assignmentTail_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (assignmentTail expression) := by
  intro input inputValid
  unfold assignmentTail
  split
  · exact (Parser.bind_invariantFreeOnValid
      (symbol_validFor .tildeEqual .statement)
      (symbol_ordinary .tildeEqual .statement).invariantFreeOnValid
      (fun operator => Parser.pure_invariantFreeOnValid
        (AssignmentTail.bitNot operator.span))) input inputValid
  · cases selected : input.peekKind?.bind valueAssignOp? with
    | none =>
        exact (Parser.rejectAt_invariantFreeOnValid
          (alpha := AssignmentTail)
          { head := .expression, tail := [] } .statement) input inputValid
    | some selectedOperator =>
        exact (Parser.bind_invariantFreeOnValid
          valueAssignOperator_validFor
          valueAssignOperator_invariantFreeOnValid
          (fun operator => Parser.bind_invariantFreeOnValid
            expressionValid expressionFree
            (fun right => Parser.pure_invariantFreeOnValid
              (AssignmentTail.value operator right)))) input inputValid

/-- Optional assignment suffix selection adds no invariant result. -/
theorem optionalAssignmentTail_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (optionalAssignmentTail expression) := by
  intro input inputValid
  unfold optionalAssignmentTail
  split
  · exact (Parser.bind_invariantFreeOnValid
      (assignmentTail_validFor expression (fun _ _ => True)
        expressionValid)
      (assignmentTail_invariantFreeOnValid expression expressionValid
        expressionFree)
      (fun tail => Parser.pure_invariantFreeOnValid (some tail)))
        input inputValid
  · exact (Parser.pure_invariantFreeOnValid none) input inputValid

/-- Optional semicolon parsing is ordinary on every valid input. -/
theorem optionalSemicolon_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalSemicolon := by
  unfold optionalSemicolon
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isSymbol observed .semicolon
  · simp only [present, if_true]
    exact Parser.bind_invariantFreeOnValid
      (symbol_validFor .semicolon .statement)
      (symbol_ordinary .semicolon .statement).invariantFreeOnValid
      (fun marker => Parser.pure_invariantFreeOnValid (some marker.span))
  · simp only [present]
    exact Parser.pure_invariantFreeOnValid none

/-- The final diagnostic/pure branch is total for every parsed prefix. -/
private theorem finishAssignmentOrExpression_invariantFreeOnValid
    (left : Expr) (tail : Option AssignmentTail)
    (semicolon : Option SourceSpan) :
    Parser.InvariantFreeOnValid (do
      let endSpan := statementEnd left tail semicolon
      let span := SourceSpan.cover left.span endSpan
      match tail with
      | some (.value operator right) =>
          if semicolon.isNone then
            let _ ← emitDiagnostic {
              span
              kind := .constraintViolation .assignmentRequiresSemicolon
            }
          pure ({
            span
            value := StatementValue.assignValue left operator right
          } : Statement)
      | some (.bitNot operator) =>
          if semicolon.isNone then
            let _ ← emitDiagnostic {
              span
              kind := .constraintViolation .assignmentRequiresSemicolon
            }
          pure ({
            span
            value := StatementValue.assignBitNot left operator
          } : Statement)
      | none => pure ({
          span
          value := StatementValue.expression left semicolon.isSome
        } : Statement)) := by
  intro input _inputValid
  dsimp only
  cases tail with
  | none => exact Or.inl ⟨_, input, rfl⟩
  | some tail =>
      cases tail with
      | value operator right =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true]
            exact Or.inl ⟨_, input.emit _, rfl⟩
          · simp only [missing]
            exact Or.inl ⟨_, input, rfl⟩
      | bitNot operator =>
          by_cases missing : semicolon.isNone
          · simp only [missing, if_true]
            exact Or.inl ⟨_, input.emit _, rfl⟩
          · simp only [missing]
            exact Or.inl ⟨_, input, rfl⟩

end StatementSimpleInternals

/--
The assignment/expression fallback is ordinary whenever expressions preserve
valid states and are ordinary on valid input.
-/
theorem assignmentOrExpressionStatement_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid
      (assignmentOrExpressionStatement expression) := by
  unfold assignmentOrExpressionStatement
  apply Parser.bind_invariantFreeOnValid expressionValid expressionFree
  intro left
  apply Parser.bind_invariantFreeOnValid
    (StatementSimpleInternals.optionalAssignmentTail_validFor expression
      (fun _ _ => True) expressionValid)
    (StatementSimpleInternals.optionalAssignmentTail_invariantFreeOnValid
      expression expressionValid expressionFree)
  intro tail
  apply Parser.bind_invariantFreeOnValid
    StatementSimpleInternals.optionalSemicolon_validFor
    StatementSimpleInternals.optionalSemicolon_invariantFreeOnValid
  intro semicolon
  exact StatementSimpleInternals.finishAssignmentOrExpression_invariantFreeOnValid
    left tail semicolon

/-- The fallback excludes every invariant result under the same premises. -/
theorem assignmentOrExpressionStatement_ne_invariant
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    assignmentOrExpressionStatement expression input ≠ .invariant error :=
  (assignmentOrExpressionStatement_invariantFreeOnValid expression
    expressionValid expressionFree).ne_invariant input inputValid error

/-- A generic element-totality contract discharges both expression premises. -/
theorem assignmentOrExpressionStatement_invariantFreeOnValid_of_elementTotality
    (expression : Parser Expr)
    (expressionTotality : ElementTotalityContract expression) :
    Parser.InvariantFreeOnValid
      (assignmentOrExpressionStatement expression) :=
  assignmentOrExpressionStatement_invariantFreeOnValid expression
    expressionTotality.validFor
    (Parser.invariantFreeOnValid_of_ne_invariant
      expressionTotality.invariantFree)

/-- Element totality directly excludes fallback invariants on valid input. -/
theorem assignmentOrExpressionStatement_ne_invariant_of_elementTotality
    (expression : Parser Expr)
    (expressionTotality : ElementTotalityContract expression)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    assignmentOrExpressionStatement expression input ≠ .invariant error :=
  (assignmentOrExpressionStatement_invariantFreeOnValid_of_elementTotality
    expression expressionTotality).ne_invariant input inputValid error

/-- Package the fallback's syntax/state laws together with its totality. -/
theorem assignmentOrExpressionStatement_totalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (expression : Parser Expr)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality : ElementTotalityContract expression) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid yulValueValid)
      (assignmentOrExpressionStatement expression) := {
  toStatementParserContract := {
    validFor := assignmentOrExpressionStatement_validFor expression
      (Expr.ValidFor statementValid) patternValueValid yulValueValid
      expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
      expressionSyntax.preservesTokenWindow
      expressionSyntax.cursorLtOnSuccess
      expressionSyntax.startsAtCurrentTokenOnSuccess
    preservesTokenWindow :=
      assignmentOrExpressionStatement_preservesTokenWindow expression
        expressionSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess :=
      assignmentOrExpressionStatement_cursorMonotoneOnSuccess expression
        expressionSyntax.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      assignmentOrExpressionStatement_startsAtCurrentTokenOnSuccess expression
        expressionSyntax.startsAtCurrentTokenOnSuccess
  }
  invariantFree :=
    assignmentOrExpressionStatement_invariantFreeOnValid_of_elementTotality
      expression expressionTotality
}

end Solcore.Syntax.Parser
