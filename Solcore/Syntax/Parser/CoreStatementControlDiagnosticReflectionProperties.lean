import Solcore.Syntax.Parser.CoreBlockSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Statement.Control

/-!
Backward propagation of diagnostic freedom through basic Core control
statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

theorem optionalElseBody_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalElseBody statement) := by
  unfold optionalElseBody
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .elseKw .statement)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
        statementReflects)
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem terminatedControl_reflectsDiagnosticFreeOnSuccess
    (keywordValue : HardKeyword) (value : StatementValue) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (terminatedControl keywordValue value) := by
  unfold terminatedControl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess keywordValue .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .statement)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser.ControlInternals

namespace Solcore.Syntax.Parser

theorem blockStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (blockStatement statement) := by
  unfold blockStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
      statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem whileStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (whileStatement statement expression) := by
  unfold whileStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .while .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftParen .statement)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
  intro condition
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .statement)
  intro closing
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
      statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem ifStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (ifStatement statement expression) := by
  unfold ifStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .ifKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftParen .statement)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
  intro condition
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .statement)
  intro closing
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
      statementReflects)
  intro thenBody
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ControlInternals.optionalElseBody_reflectsDiagnosticFreeOnSuccess
      statement statementReflects)
  intro elseBody
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem breakStatement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess breakStatement :=
  ControlInternals.terminatedControl_reflectsDiagnosticFreeOnSuccess
    .breakKw .breakStmt

theorem continueStatement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess continueStatement :=
  ControlInternals.terminatedControl_reflectsDiagnosticFreeOnSuccess
    .continueKw .continueStmt

end Solcore.Syntax.Parser
