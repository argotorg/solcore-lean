import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Statement.Simple
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties

/-!
Backward propagation of diagnostic freedom through Core `let` and `return`
statement components.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

theorem optionalSemicolon_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess optionalSemicolon := by
  unfold optionalSemicolon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .statement)
    intro semicolon
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem optionalReturnValue_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalReturnValue expression) := by
  unfold optionalReturnValue
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
    intro value
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem optionalLetType_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess optionalLetType := by
  unfold optionalLetType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .colon .statement)
    intro colon
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      typeExpr_reflectsDiagnosticFreeOnSuccess
    intro type
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem optionalLetInitializer_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalLetInitializer expression) := by
  unfold optionalLetInitializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .equal .statement)
    intro equal
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess expressionReflects
    intro value
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem letStatement_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess (letStatement expression) := by
  unfold letStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .letKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .statement)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    StatementSimpleInternals.optionalLetType_reflectsDiagnosticFreeOnSuccess
  intro type
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (StatementSimpleInternals.optionalLetInitializer_reflectsDiagnosticFreeOnSuccess
      expression expressionReflects)
  intro initializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .statement)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

theorem returnStatement_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess (returnStatement expression) := by
  unfold returnStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .returnKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (StatementSimpleInternals.optionalReturnValue_reflectsDiagnosticFreeOnSuccess
      expression expressionReflects)
  intro value
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .statement)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
