import Solcore.Syntax.Parser.TermStatementTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties

/-! Totality for the non-recovering `let` and `return` statement branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

theorem optionalLetType_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalLetType := by
  unfold optionalLetType
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  split
  · apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .colon .statement)
      (symbol_ordinary .colon .statement).invariantFreeOnValid
    intro colon
    apply Parser.bind_invariantFreeOnValid typeExpr_validFor
      typeExpr_invariantFreeOnValid
    intro type
    exact Parser.pure_invariantFreeOnValid (some type)
  · exact Parser.pure_invariantFreeOnValid none

theorem optionalLetInitializer_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (optionalLetInitializer expression) := by
  unfold optionalLetInitializer
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  split
  · apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .equal .statement)
      (symbol_ordinary .equal .statement).invariantFreeOnValid
    intro equal
    apply Parser.bind_invariantFreeOnValid expressionValid expressionFree
    intro value
    exact Parser.pure_invariantFreeOnValid (some value)
  · exact Parser.pure_invariantFreeOnValid none

theorem optionalReturnValue_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (optionalReturnValue expression) := by
  unfold optionalReturnValue
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  split
  · exact Parser.pure_invariantFreeOnValid none
  · apply Parser.bind_invariantFreeOnValid expressionValid expressionFree
    intro value
    exact Parser.pure_invariantFreeOnValid (some value)

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem letStatement_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (letStatement expression) := by
  unfold letStatement
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .letKw .statement)
    (keyword_ordinary .letKw .statement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid (identifier_validFor .statement)
    (identifier_ordinary .statement).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    StatementSimpleInternals.optionalLetType_validFor
    StatementSimpleInternals.optionalLetType_invariantFreeOnValid
  intro type
  apply Parser.bind_invariantFreeOnValid
    (StatementSimpleInternals.optionalLetInitializer_validFor expression
      (fun _ _ => True) expressionValid)
    (StatementSimpleInternals.optionalLetInitializer_invariantFreeOnValid
      expression expressionValid expressionFree)
  intro initializer
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .statement)
    (symbol_ordinary .semicolon .statement).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span semicolon.span
    value := .letDecl name type initializer
  } : Statement)

theorem returnStatement_invariantFreeOnValid
    (expression : Parser Expr)
    (expressionValid : expression.ValidFor (fun _ _ => True))
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    Parser.InvariantFreeOnValid (returnStatement expression) := by
  unfold returnStatement
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .returnKw .statement)
    (keyword_ordinary .returnKw .statement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (StatementSimpleInternals.optionalReturnValue_validFor expression
      (fun _ _ => True) expressionValid)
    (StatementSimpleInternals.optionalReturnValue_invariantFreeOnValid
      expression expressionValid expressionFree)
  intro value
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .statement)
    (symbol_ordinary .semicolon .statement).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span semicolon.span
    value := .returnStmt value
  } : Statement)

theorem letStatement_totalityContract
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        YulStmt.ValidFor)
      (letStatement expression) := {
  validFor := letStatement_validFor expression expressionValueValid
    patternValueValid YulStmt.ValidFor expressionValid expressionWindow
      expressionCursor
  preservesTokenWindow := letStatement_preservesTokenWindow expression
    expressionWindow
  cursorMonotoneOnSuccess := letStatement_cursorMonotoneOnSuccess expression
    expressionCursor
  startsAtCurrentTokenOnSuccess :=
    letStatement_startsAtCurrentTokenOnSuccess expression
  invariantFree := letStatement_invariantFreeOnValid expression
    (expressionValid.mono (fun _ _ _ => trivial)) expressionFree
}

theorem returnStatement_totalityContract
    (expression : Parser Expr)
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (expressionValid : expression.ValidFor expressionValueValid)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    (expressionFree : Parser.InvariantFreeOnValid expression) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        YulStmt.ValidFor)
      (returnStatement expression) := {
  validFor := returnStatement_validFor expression expressionValueValid
    patternValueValid YulStmt.ValidFor expressionValid expressionWindow
      expressionCursor
  preservesTokenWindow := returnStatement_preservesTokenWindow expression
    expressionWindow
  cursorMonotoneOnSuccess := returnStatement_cursorMonotoneOnSuccess
    expression expressionCursor
  startsAtCurrentTokenOnSuccess :=
    returnStatement_startsAtCurrentTokenOnSuccess expression
  invariantFree := returnStatement_invariantFreeOnValid expression
    (expressionValid.mono (fun _ _ _ => trivial)) expressionFree
}

end Solcore.Syntax.Parser
