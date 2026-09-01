import Solcore.Syntax.Parser.YulBlockDiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulExpressionLeafSoundnessProperties
import Solcore.Syntax.Parser.YulNamesDiagnosticReflectionProperties
import Solcore.Syntax.Parser.Yul.Control

/-! Diagnostic reflection for inline-Yul function signatures and bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The allow-empty Yul parameter list reflects through every strict name. -/
theorem yulParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulParameters :=
  delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
    yulName .yulStatement .yul yulName_reflectsDiagnosticFreeOnSuccess

namespace YulControl

/-- A return clause reflects through its arrow and nonempty name sequence. -/
theorem returnClause_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess returnClause := by
  unfold returnClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .arrow .yulStatement)
  intro arrow
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulNames_reflectsDiagnosticFreeOnSuccess
  intro names
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Optional returns reflect through the preferred arrow branch. -/
theorem returns_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess returns := by
  unfold returns
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      returnClause_reflectsDiagnosticFreeOnSuccess
    intro clause
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end YulControl

/-- Complete function parsing reflects through signature and recursive body. -/
theorem yulFunctionStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulFunctionStatement statement) := by
  unfold yulFunctionStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .functionKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulName_reflectsDiagnosticFreeOnSuccess
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    YulControl.returns_reflectsDiagnosticFreeOnSuccess
  intro returns
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
