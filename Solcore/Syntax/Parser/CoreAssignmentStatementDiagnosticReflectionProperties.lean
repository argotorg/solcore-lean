import Solcore.Syntax.Parser.CoreStatementSimpleDiagnosticReflectionProperties

/-!
Backward propagation of diagnostic freedom through Core assignment and
expression statement parsing.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

/-- Value-assignment operator consumption never removes diagnostics. -/
theorem valueAssignOperator_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess valueAssignOperator := by
  intro input operator next result diagnosticFree
  unfold valueAssignOperator at result
  cases found : input.peek? with
  | none => simp [found, rejectAt] at result
  | some token =>
      simp only [found] at result
      cases decoded : valueAssignOp? token.value with
      | none => simp [decoded, rejectAt] at result
      | some value =>
          simp only [decoded] at result
          cases result
          exact diagnosticFree

/-- Assignment-tail success reflects through a possible right expression. -/
theorem assignmentTail_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess (assignmentTail expression) := by
  intro input tail next result diagnosticFree
  unfold assignmentTail at result
  by_cases bitNot : isSymbol input .tildeEqual
  · simp only [bitNot, if_true] at result
    exact (Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .tildeEqual .statement)
      (fun operator => Parser.pure_reflectsDiagnosticFreeOnSuccess
        (AssignmentTail.bitNot operator.span))) input tail next result
          diagnosticFree
  · have bitNotFalse : isSymbol input .tildeEqual = false :=
      Bool.eq_false_iff.mpr bitNot
    simp only [bitNotFalse, Bool.false_eq_true, if_false] at result
    cases decoded : input.peekKind?.bind valueAssignOp? with
    | none => rw [decoded] at result; unfold rejectAt at result; contradiction
    | some operator =>
        rw [decoded] at result
        exact (Parser.bind_reflectsDiagnosticFreeOnSuccess
          valueAssignOperator_reflectsDiagnosticFreeOnSuccess
          (fun located => Parser.bind_reflectsDiagnosticFreeOnSuccess
            expressionReflects
            (fun right => Parser.pure_reflectsDiagnosticFreeOnSuccess
              (AssignmentTail.value located right)))) input tail next result
                diagnosticFree

/-- Optional assignment-tail parsing reflects through its committed branch. -/
theorem optionalAssignmentTail_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalAssignmentTail expression) := by
  intro input tail next result diagnosticFree
  unfold optionalAssignmentTail at result
  split at result
  · exact (Parser.bind_reflectsDiagnosticFreeOnSuccess
      (assignmentTail_reflectsDiagnosticFreeOnSuccess expression
        expressionReflects)
      (fun value => Parser.pure_reflectsDiagnosticFreeOnSuccess (some value)))
        input tail next result diagnosticFree
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none input tail next
      result diagnosticFree

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

/-- The complete fallback statement reflects through every successful stage. -/
theorem assignmentOrExpressionStatement_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (assignmentOrExpressionStatement expression) := by
  intro input statement next result diagnosticFree
  unfold assignmentOrExpressionStatement at result
  simp only [bind] at result
  cases leftResult : expression input with
  | reject failure rejected => simp [leftResult] at result
  | invariant error => simp [leftResult] at result
  | ok left afterLeft =>
      simp only [leftResult] at result
      cases tailResult : StatementSimpleInternals.optionalAssignmentTail
          expression afterLeft with
      | reject failure rejected => simp [tailResult] at result
      | invariant error => simp [tailResult] at result
      | ok tail afterTail =>
          simp only [tailResult] at result
          cases semicolonResult : StatementSimpleInternals.optionalSemicolon
              afterTail with
          | reject failure rejected => simp [semicolonResult] at result
          | invariant error => simp [semicolonResult] at result
          | ok semicolon afterSemicolon =>
              simp only [semicolonResult] at result
              have afterSemicolonFree : afterSemicolon.diagnosticsRev = [] := by
                cases tail with
                | none => cases result; exact diagnosticFree
                | some tail =>
                    cases tail with
                    | value operator right =>
                        by_cases missing : semicolon.isNone
                        · simp only [missing, if_true, emitDiagnostic,
                            modifyState, pure] at result
                          cases result
                          simp [State.emit] at diagnosticFree
                        · simp only [missing, Bool.false_eq_true, if_false,
                            pure] at result
                          cases result
                          exact diagnosticFree
                    | bitNot operator =>
                        by_cases missing : semicolon.isNone
                        · simp only [missing, if_true, emitDiagnostic,
                            modifyState, pure] at result
                          cases result
                          simp [State.emit] at diagnosticFree
                        · simp only [missing, Bool.false_eq_true, if_false,
                            pure] at result
                          cases result
                          exact diagnosticFree
              have afterTailFree :=
                StatementSimpleInternals.optionalSemicolon_reflectsDiagnosticFreeOnSuccess
                  afterTail semicolon afterSemicolon semicolonResult
                    afterSemicolonFree
              have afterLeftFree :=
                StatementSimpleInternals.optionalAssignmentTail_reflectsDiagnosticFreeOnSuccess
                  expression expressionReflects afterLeft tail afterTail
                    tailResult afterTailFree
              exact expressionReflects input left afterLeft leftResult
                afterLeftFree

end Solcore.Syntax.Parser
