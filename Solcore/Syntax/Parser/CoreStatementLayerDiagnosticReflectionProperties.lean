import Solcore.Syntax.Parser.CoreAssemblyStatementDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreAssignmentStatementDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreForItemsDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreMatchStatementDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreStatementControlDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreStatementFallbackDiagnosticProperties
import Solcore.Syntax.Parser.CoreStatementSimpleDiagnosticReflectionProperties

/-! Diagnostic reflection for the prioritized Core statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- The full statement layer cannot erase diagnostics on successful parsing. -/
theorem statementLayer_reflectsDiagnosticFreeOnSuccess
    (nestedStatement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nestedStatement)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern)
    (yulBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess yulBody) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (statementLayer nestedStatement expression pattern) := by
  intro input value next result diagnosticFree
  unfold statementLayer at result
  split at result
  · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
      (letStatement expression) (assignmentOrExpressionStatement expression)
        (letStatement_reflectsDiagnosticFreeOnSuccess expression
          expressionReflects) input value next result diagnosticFree
  · split at result
    · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
        (returnStatement expression)
          (assignmentOrExpressionStatement expression)
          (returnStatement_reflectsDiagnosticFreeOnSuccess expression
            expressionReflects) input value next result diagnosticFree
    · split at result
      · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
          (matchStatement nestedStatement expression pattern)
            (assignmentOrExpressionStatement expression)
            (matchStatement_reflectsDiagnosticFreeOnSuccess nestedStatement
              expression pattern nestedReflects expressionReflects
                patternReflects) input value next result diagnosticFree
      · split at result
        · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
            (forStatement nestedStatement expression)
              (assignmentOrExpressionStatement expression)
              (forStatement_reflectsDiagnosticFreeOnSuccess nestedStatement
                expression nestedReflects expressionReflects) input value next
                  result diagnosticFree
        · split at result
          · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
              (whileStatement nestedStatement expression)
                (assignmentOrExpressionStatement expression)
                (whileStatement_reflectsDiagnosticFreeOnSuccess
                  nestedStatement expression nestedReflects expressionReflects)
                    input value next result diagnosticFree
          · split at result
            · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                (ifStatement nestedStatement expression)
                  (assignmentOrExpressionStatement expression)
                  (ifStatement_reflectsDiagnosticFreeOnSuccess nestedStatement
                    expression nestedReflects expressionReflects) input value
                      next result diagnosticFree
            · split at result
              · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                  assemblyStatement (assignmentOrExpressionStatement expression)
                    (assemblyStatement_reflectsDiagnosticFreeOnSuccess
                      yulBodyReflects) input value next result diagnosticFree
              · split at result
                · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                    (blockStatement nestedStatement)
                      (assignmentOrExpressionStatement expression)
                      (blockStatement_reflectsDiagnosticFreeOnSuccess
                        nestedStatement nestedReflects) input value next result
                          diagnosticFree
                · split at result
                  · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                      breakStatement (assignmentOrExpressionStatement expression)
                        breakStatement_reflectsDiagnosticFreeOnSuccess input
                          value next result diagnosticFree
                  · split at result
                    · exact recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                        continueStatement
                          (assignmentOrExpressionStatement expression)
                          continueStatement_reflectsDiagnosticFreeOnSuccess
                            input value next result diagnosticFree
                    · exact
                        assignmentOrExpressionStatement_reflectsDiagnosticFreeOnSuccess
                          expression expressionReflects input value next result
                            diagnosticFree

end Solcore.Syntax.Parser.TermInternals
