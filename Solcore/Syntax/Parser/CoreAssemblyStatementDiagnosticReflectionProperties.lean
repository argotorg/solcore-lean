import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Statement.Control

/-!
Diagnostic reflection for the Core wrapper around an inline-Yul body.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem assemblyStatement_reflectsDiagnosticFreeOnSuccess
    (yulBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess yulBody) :
    Parser.ReflectsDiagnosticFreeOnSuccess assemblyStatement := by
  unfold assemblyStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .assemblyKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess yulBodyReflects
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
