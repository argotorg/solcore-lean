import Solcore.Syntax.Parser.CoreMatchComponentDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreMatchValidationSoundnessProperties

/-! Diagnostic reflection for complete canonical Core `match` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A complete Core `match` success cannot erase an earlier diagnostic. -/
theorem matchStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (matchStatement statement expression pattern) := by
  unfold matchStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .matchKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen false
      expression .expression .statement expressionReflects)
  intro values
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (MatchInternals.requireScrutinees_reflectsDiagnosticFreeOnSuccess values)
  intro scrutinees
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftBrace .statement)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (MatchInternals.matchCasesFromCurrentState_reflectsDiagnosticFreeOnSuccess
      statement pattern statementReflects patternReflects)
  intro cases
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (MatchInternals.optionalDefaultBody_reflectsDiagnosticFreeOnSuccess
      statement statementReflects)
  intro defaultBody
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightBrace .statement)
  intro closing
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (MatchInternals.validateMatchArities_reflectsDiagnosticFreeOnSuccess
      scrutinees.elements.toList.length cases)
  intro checked
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
