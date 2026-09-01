import Solcore.Syntax.Parser.YulBlockDiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulExpressionLeafSoundnessProperties
import Solcore.Syntax.Parser.YulStatementBasicDiagnosticReflectionProperties
import Solcore.Syntax.Parser.Yul.Control

/-! Diagnostic reflection for inline-Yul switch parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulControl

/-- One case arm reflects through its literal and recursive block. -/
theorem caseArm_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (caseArm statement) := by
  unfold caseArm
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .caseKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulLiteral_reflectsDiagnosticFreeOnSuccess
  intro literal
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- The maximal case loop reflects through every committed case arm. -/
theorem caseList_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    ∀ fuel casesRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (caseList statement fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases next result diagnosticFree
      simp [caseList] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases next result diagnosticFree
      unfold caseList at result
      split at result
      · cases armResult : caseArm statement input with
        | invariant error => simp [armResult] at result
        | reject failure rejected => simp [armResult] at result
        | ok arm afterArm =>
            simp only [armResult] at result
            split at result
            · have afterArmFree := inductionHypothesis (arm :: casesRev)
                afterArm cases next result diagnosticFree
              exact caseArm_reflectsDiagnosticFreeOnSuccess statement
                statementReflects input arm afterArm armResult afterArmFree
            · contradiction
      · cases result
        exact diagnosticFree

/-- Optional default parsing reflects through its preferred keyword branch. -/
theorem optionalDefault_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess (optionalDefault statement) := by
  unfold optionalDefault
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (yulBlock_reflectsDiagnosticFreeOnSuccess statement statementReflects)
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end YulControl

/-- Complete switch parsing reflects diagnostic freedom.  The no-case branch
has no diagnostic-free success because it always emits the switch constraint. -/
theorem yulSwitchStatement_reflectsDiagnosticFreeOnSuccess
    (statement : Parser YulStmt)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (yulSwitchStatement statement) := by
  unfold yulSwitchStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .switchKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro scrutinee
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
  · intro input cases next result diagnosticFree
    exact YulControl.caseList_reflectsDiagnosticFreeOnSuccess statement
      statementReflects (input.remainingCount + 1) [] input cases next result
        diagnosticFree
  intro cases
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (YulControl.optionalDefault_reflectsDiagnosticFreeOnSuccess statement
      statementReflects)
  intro defaultBody
  cases cases with
  | cons head tail => exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  | nil =>
      apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
      intro emitted
      exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
