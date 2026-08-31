import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.TermStatementFallbackTotalityProperties

/-! Recursive-fuel totality for the terminal Core-statement fallback. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace StatementSimpleInternals

/-- Assignment suffixes remain ordinary below the expression fuel bound. -/
theorem assignmentTail_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ tail next, assignmentTail expression input = .ok tail next) ∨
    (∃ failure next,
      assignmentTail expression input = .reject failure next) := by
  unfold assignmentTail
  split
  · rcases (symbol_ordinary .tildeEqual .statement) input with
      ⟨operator, next, operatorResult⟩ |
      ⟨failure, rejected, operatorResult⟩
    · exact Or.inl ⟨AssignmentTail.bitNot operator.span, next, by
        simp only [bind, operatorResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [bind, operatorResult]⟩
  · cases selected : input.peekKind?.bind valueAssignOp? with
    | none =>
        exact (Parser.rejectAt_invariantFreeOnValid
          (alpha := AssignmentTail)
          { head := .expression, tail := [] } .statement) input inputValid
    | some selectedOperator =>
        rcases valueAssignOperator_invariantFreeOnValid input inputValid with
          ⟨operator, afterOperator, operatorResult⟩ |
          ⟨failure, rejected, operatorResult⟩
        · have operatorReply := valueAssignOperator_validFor input inputValid
          rw [operatorResult] at operatorReply
          have operatorWindow := valueAssignOperator_preservesTokenWindow input
          rw [operatorResult] at operatorWindow
          have expressionAdequate :
              afterOperator.remainingCount < expressionFuel :=
            remainingCount_lt_of_cursor_le operatorWindow.2
              (valueAssignOperator_cursorMonotoneOnSuccess input operator
                afterOperator operatorResult) adequate
          rcases contract.ordinary afterOperator operatorReply.2.1
              expressionAdequate with
            ⟨right, final, rightResult⟩ |
            ⟨failure, rejected, rightResult⟩
          · exact Or.inl ⟨AssignmentTail.value operator right, final, by
              simp only [bind, operatorResult, rightResult, pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [bind, operatorResult, rightResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [bind, operatorResult]⟩

/-- Optional suffix selection preserves the same expression-fuel bound. -/
theorem optionalAssignmentTail_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ tail next,
      optionalAssignmentTail expression input = .ok tail next) ∨
    (∃ failure next,
      optionalAssignmentTail expression input = .reject failure next) := by
  unfold optionalAssignmentTail
  split
  · rcases assignmentTail_ordinary_of_expressionFuel expression
        expressionFuel contract input inputValid adequate with
      ⟨tail, next, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · exact Or.inl ⟨some tail, next, by
        simp only [bind, tailResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [bind, tailResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

end StatementSimpleInternals

/--
The fallback stays ordinary below the expression fuel bound. A successful
left expression preserves the bound for a possible assignment right-hand
expression through its token-window and cursor contracts.
-/
theorem assignmentOrExpressionStatement_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ statement next,
      assignmentOrExpressionStatement expression input = .ok statement next) ∨
    (∃ failure next,
      assignmentOrExpressionStatement expression input =
        .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨left, afterLeft, leftResult⟩ |
    ⟨failure, rejected, leftResult⟩
  · have leftReply := contract.validFor input inputValid
    rw [leftResult] at leftReply
    have leftWindow := contract.preservesTokenWindow input
    rw [leftResult] at leftWindow
    have tailAdequate : afterLeft.remainingCount < expressionFuel :=
      remainingCount_lt_of_cursor_le leftWindow.2
        (Nat.le_of_lt (contract.cursorLtOnSuccess leftResult)) adequate
    rcases StatementSimpleInternals.optionalAssignmentTail_ordinary_of_expressionFuel
        expression expressionFuel contract afterLeft leftReply.2.1
          tailAdequate with
      ⟨tail, afterTail, tailResult⟩ |
      ⟨failure, rejected, tailResult⟩
    · have tailReply :=
        StatementSimpleInternals.optionalAssignmentTail_validFor expression
          (fun _ _ => True) contract.validFor afterLeft leftReply.2.1
      rw [tailResult] at tailReply
      rcases StatementSimpleInternals.optionalSemicolon_invariantFreeOnValid
          afterTail tailReply.2.1 with
        ⟨semicolon, afterSemicolon, semicolonResult⟩ |
        ⟨failure, rejected, semicolonResult⟩
      · let endSpan := StatementSimpleInternals.statementEnd left tail semicolon
        let span := SourceSpan.cover left.span endSpan
        cases tail with
        | none =>
            exact Or.inl ⟨{
              span
              value := .expression left semicolon.isSome
            }, afterSemicolon, by
              simp only [assignmentOrExpressionStatement, bind, leftResult,
                tailResult, semicolonResult, pure]
              rfl⟩
        | some tail =>
            cases tail with
            | value operator right =>
                let statement : Statement := {
                  span
                  value := .assignValue left operator right
                }
                by_cases missing : semicolon.isNone
                · exact Or.inl ⟨statement, afterSemicolon.emit {
                      span
                      kind := .constraintViolation
                        .assignmentRequiresSemicolon
                    }, by
                    simp only [assignmentOrExpressionStatement, leftResult,
                      tailResult, semicolonResult, missing, if_true,
                      emitDiagnostic, modifyState, bind, pure]
                    rfl⟩
                · exact Or.inl ⟨statement, afterSemicolon, by
                    simp only [assignmentOrExpressionStatement, bind,
                      leftResult, tailResult, semicolonResult, missing, pure]
                    rfl⟩
            | bitNot operator =>
                let statement : Statement := {
                  span
                  value := .assignBitNot left operator
                }
                by_cases missing : semicolon.isNone
                · exact Or.inl ⟨statement, afterSemicolon.emit {
                      span
                      kind := .constraintViolation
                        .assignmentRequiresSemicolon
                    }, by
                    simp only [assignmentOrExpressionStatement, leftResult,
                      tailResult, semicolonResult, missing, if_true,
                      emitDiagnostic, modifyState, bind, pure]
                    rfl⟩
                · exact Or.inl ⟨statement, afterSemicolon, by
                    simp only [assignmentOrExpressionStatement, bind,
                      leftResult, tailResult, semicolonResult, missing, pure]
                    rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [assignmentOrExpressionStatement, bind, leftResult,
            tailResult, semicolonResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [assignmentOrExpressionStatement, bind, leftResult,
          tailResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [assignmentOrExpressionStatement, bind, leftResult]⟩

/-- The fuel-bounded fallback cannot expose an invariant reply. -/
theorem assignmentOrExpressionStatement_ne_invariant_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel)
    (error : ParserInvariantError) :
    assignmentOrExpressionStatement expression input ≠ .invariant error := by
  intro failed
  rcases assignmentOrExpressionStatement_ordinary_of_expressionFuel expression
      expressionFuel contract input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

namespace TermInternals

/-- Statement syntax/state laws paired with fuel-bounded ordinary control. -/
structure FuelStatementTotalityContract
    (valueValid : SourceFile → Statement → Prop)
    (parser : Parser Statement) (fuel : Nat) : Prop
    extends StatementParserContract valueValid parser where
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace FuelStatementTotalityContract

/-- Adequate fuel excludes every statement-parser invariant. -/
theorem ne_invariant
    {valueValid : SourceFile → Statement → Prop}
    {parser : Parser Statement} {fuel : Nat}
    (contract : FuelStatementTotalityContract valueValid parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end FuelStatementTotalityContract
end TermInternals

/-- Package the recursive fallback with its fixed expression-fuel bound. -/
theorem assignmentOrExpressionStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (expression : Parser Expr) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid yulValueValid)
      (assignmentOrExpressionStatement expression) expressionFuel := {
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
  ordinary := assignmentOrExpressionStatement_ordinary_of_expressionFuel
    expression expressionFuel expressionTotality
}

end Solcore.Syntax.Parser
