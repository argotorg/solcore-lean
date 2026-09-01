import Solcore.Syntax.Parser.YulBlockDiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulStatementBasicDiagnosticReflectionProperties

/-!
Diagnostic reflection for Yul block, `if`, and `for` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem yulBlockStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulBlockStatement statement) := by
  unfold yulBlockStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem yulIfStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulIfStatement statement) := by
  unfold yulIfStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .ifKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro condition
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem yulForStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulForStatement statement) := by
  unfold yulForStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .forKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro initializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro condition
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro post
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
