import Solcore.Syntax.Parser.CoreBlockSoundnessProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Statement.Match

/-! Diagnostic reflection for Core-match parsing components. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Nonempty scrutinee refinement cannot erase diagnostics. -/
theorem requireScrutinees_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList Expr) :
    Parser.ReflectsDiagnosticFreeOnSuccess (requireScrutinees values) := by
  intro input scrutinees next result diagnosticFree
  unfold requireScrutinees at result
  cases elements : values.elements with
  | nil => simp [elements, rejectAt] at result
  | cons head tail =>
      simp only [elements, pure] at result
      cases result
      exact diagnosticFree

/-- One case reflects through its pattern and required-tail body. -/
theorem matchCase_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess (matchCase statement pattern) := by
  unfold matchCase
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .caseKw .statement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess patternReflects
  intro retainedPattern
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
      statementReflects)
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- The maximal case loop reflects through every parsed arm. -/
theorem matchCases_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern) :
    ∀ fuel casesRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (matchCases statement pattern fuel casesRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro casesRev input cases next result diagnosticFree
      simp [matchCases] at result
  | succ fuel inductionHypothesis =>
      intro casesRev input cases next result diagnosticFree
      unfold matchCases at result
      split at result
      · cases caseResult : matchCase statement pattern input with
        | invariant error => simp [caseResult] at result
        | reject failure rejected => simp [caseResult] at result
        | ok arm afterCase =>
            simp only [caseResult] at result
            split at result
            · have afterCaseFree := inductionHypothesis (arm :: casesRev)
                afterCase cases next result diagnosticFree
              exact matchCase_reflectsDiagnosticFreeOnSuccess statement pattern
                statementReflects patternReflects input arm afterCase
                  caseResult afterCaseFree
            · contradiction
      · cases result
        exact diagnosticFree

/-- The statement-facing loop chooses its fuel from the current remainder. -/
theorem matchCasesFromCurrentState_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement) (pattern : Parser Pattern)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (patternReflects : Parser.ReflectsDiagnosticFreeOnSuccess pattern) :
    Parser.ReflectsDiagnosticFreeOnSuccess (fun state =>
      matchCases statement pattern (state.remainingCount + 1) [] state) := by
  intro input cases next result diagnosticFree
  exact matchCases_reflectsDiagnosticFreeOnSuccess statement pattern
    statementReflects patternReflects (input.remainingCount + 1) [] input cases
      next result diagnosticFree

/-- Optional default parsing reflects through its required-tail block. -/
theorem optionalDefaultBody_reflectsDiagnosticFreeOnSuccess
    (statement : Parser Statement)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalDefaultBody statement) := by
  unfold optionalDefaultBody
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess .defaultKw .statement)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (coreBlock_reflectsDiagnosticFreeOnSuccess statement .require
        statementReflects)
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

end Solcore.Syntax.Parser.MatchInternals
