import Solcore.Syntax.Parser.CoreYulStatementBasicSoundnessProperties
import Solcore.Syntax.Parser.CoreYulStatementRecoveryDiagnosticProperties
import Solcore.Syntax.Parser.YulFunctionDiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulStatementControlDiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulSwitchDiagnosticReflectionProperties

/-! Diagnostic reflection for public Yul statement parsing layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The complete ordered non-terminating Yul dispatcher reflects diagnostics. -/
theorem yulStatementCore_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulStmt)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulStatementCore nested) := by
  intro input value next result diagnosticFree
  unfold yulStatementCore at result
  split at result
  · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
      (yulBlockStatement nested) yulExpressionStatement
        (yulBlockStatement_reflectsDiagnosticFreeOnSuccess nested
          nestedReflects) input value next result diagnosticFree
  · split at result
    · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
        yulLetStatement yulExpressionStatement
          yulLetStatement_reflectsDiagnosticFreeOnSuccess input value next
            result diagnosticFree
    · split at result
      · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
          (yulIfStatement nested) yulExpressionStatement
            (yulIfStatement_reflectsDiagnosticFreeOnSuccess nested
              nestedReflects) input value next result diagnosticFree
      · split at result
        · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
            (yulForStatement nested) yulExpressionStatement
              (yulForStatement_reflectsDiagnosticFreeOnSuccess nested
                nestedReflects) input value next result diagnosticFree
        · split at result
          · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
              (yulSwitchStatement nested) yulExpressionStatement
                (yulSwitchStatement_reflectsDiagnosticFreeOnSuccess nested
                  nestedReflects) input value next result diagnosticFree
          · split at result
            · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                (yulFunctionStatement nested) yulExpressionStatement
                  (yulFunctionStatement_reflectsDiagnosticFreeOnSuccess nested
                    nestedReflects) input value next result diagnosticFree
            · split at result
              · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                  yulReturnBuiltin yulExpressionStatement
                    yulReturnBuiltin_reflectsDiagnosticFreeOnSuccess input
                      value next result diagnosticFree
              · split at result
                · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                    (yulControlToken .leaveKw .leave) yulExpressionStatement
                      (yulControlToken_reflectsDiagnosticFreeOnSuccess .leaveKw
                        .leave) input value next result diagnosticFree
                · split at result
                  · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                      (yulControlToken .breakKw .break) yulExpressionStatement
                        (yulControlToken_reflectsDiagnosticFreeOnSuccess
                          .breakKw .break) input value next result diagnosticFree
                  · split at result
                    · exact recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
                        (yulControlToken .continueKw .continue)
                          yulExpressionStatement
                          (yulControlToken_reflectsDiagnosticFreeOnSuccess
                            .continueKw .continue) input value next result
                              diagnosticFree
                    · split at result
                      · exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
                          yulAssignment_reflectsDiagnosticFreeOnSuccess
                          yulExpressionStatement_reflectsDiagnosticFreeOnSuccess
                            input value next result diagnosticFree
                      · exact
                          yulExpressionStatement_reflectsDiagnosticFreeOnSuccess
                            input value next result diagnosticFree

/-- The concrete optional-semicolon layer reflects through its exact core. -/
theorem yulStatementTerminated_reflectsDiagnosticFreeOnSuccess_of_core
    (nested : Parser YulStmt)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulStatementTerminated nested) := by
  unfold yulStatementTerminated
  exact yulStatementTerminated_reflectsDiagnosticFreeOnSuccess
    (yulStatementCore nested)
      (yulStatementCore_reflectsDiagnosticFreeOnSuccess nested nestedReflects)

/-- Clean recovery-layer success reflects through the terminated parser. -/
theorem yulStatementLayer_reflectsDiagnosticFreeOnSuccess_of_core
    (nested : Parser YulStmt)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulStatementLayer nested) :=
  yulStatementLayer_reflectsDiagnosticFreeOnSuccess nested
    (yulStatementTerminated_reflectsDiagnosticFreeOnSuccess_of_core nested
      nestedReflects)

end Solcore.Syntax.Parser
