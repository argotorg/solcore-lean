import Solcore.Syntax.Parser.CoreExpressionAtomLeafSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionCollectionAtomDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreExpressionDotConstructorSoundnessProperties
import Solcore.Syntax.Parser.CoreLambdaExpressionSoundnessProperties

/-! Diagnostic reflection for the ordered Core expression-atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/--
The seven-way Core atom dispatcher cannot erase diagnostics when its supplied
recursive expression and block parsers cannot erase them.
-/
theorem expressionAtomCore_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtomCore nested block) := by
  intro input value next result diagnosticFree
  unfold expressionAtomCore at result
  split at result
  · exact literalExpression_reflectsDiagnosticFreeOnSuccess input value next
      result diagnosticFree
  split at result
  · exact identifierExpression_reflectsDiagnosticFreeOnSuccess input value
      next result diagnosticFree
  split at result
  · exact dotConstructor_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects input value next result diagnosticFree
  split at result
  · exact proxyExpression_reflectsDiagnosticFreeOnSuccess input value next
      result diagnosticFree
  split at result
  · exact parenthesized_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects input value next result diagnosticFree
  split at result
  · exact arrayLiteral_reflectsDiagnosticFreeOnSuccess nested nestedReflects
      input value next result diagnosticFree
  split at result
  · exact lambdaExpression_reflectsDiagnosticFreeOnSuccess block
      blockReflects input value next result diagnosticFree
  · simp [rejectAt] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
