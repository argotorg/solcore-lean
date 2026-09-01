import Solcore.Syntax.Parser.CoreAssignmentStatementDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreStatementSimpleDiagnosticReflectionProperties
import Solcore.Syntax.Parser.Statement.Simple

/-!
Backward propagation of diagnostic freedom through Core `for` header items.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

theorem forLetItem_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess (forLetItem expression) := by
  unfold forLetItem
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .letKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .statement)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalLetType_reflectsDiagnosticFreeOnSuccess
  intro type
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalLetInitializer_reflectsDiagnosticFreeOnSuccess expression
      expressionReflects)
  intro initializer
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem forAssignmentOrExpression_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (forAssignmentOrExpression expression) := by
  unfold forAssignmentOrExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
  intro left
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalAssignmentTail_reflectsDiagnosticFreeOnSuccess expression
      expressionReflects)
  intro tail
  cases tail with
  | none => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  | some tail =>
      cases tail <;> exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem forItem_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess (forItem expression) := by
  intro input item next result diagnosticFree
  unfold forItem at result
  split at result
  · exact
      (StatementSimpleInternals.forLetItem_reflectsDiagnosticFreeOnSuccess
        expression expressionReflects) input item next result diagnosticFree
  · exact
      (StatementSimpleInternals.forAssignmentOrExpression_reflectsDiagnosticFreeOnSuccess
        expression expressionReflects) input item next result diagnosticFree

end Solcore.Syntax.Parser
