import Solcore.Syntax.Parser.SignatureLeafDiagnosticReflectionProperties

/-! Diagnostic-free reflection for complete named-function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Complete signature parsing cannot erase an incoming diagnostic. -/
theorem functionSignature_reflectsDiagnosticFreeOnSuccess
    (location : FunctionLocation) :
    Parser.ReflectsDiagnosticFreeOnSuccess (functionSignature location) := by
  unfold functionSignature
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .functionKw .topItem)
  intro functionToken
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalGenericParameters_reflectsDiagnosticFreeOnSuccess
  intro genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    functionParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (functionModifiers_reflectsDiagnosticFreeOnSuccess location)
  intro modifiers
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    returnClause_reflectsDiagnosticFreeOnSuccess
  intro returnsClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    whereClause_reflectsDiagnosticFreeOnSuccess
  intro whereClause
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
