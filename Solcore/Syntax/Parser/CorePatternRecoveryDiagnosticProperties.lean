import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Pattern

/-!
Diagnostic commitments at the public Core pattern recovery boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Finishing a recovered pattern always commits its recovery diagnostic. -/
theorem finishRecoveredPattern_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) {input next : State} {value : Pattern}
    (result : finishRecoveredPattern first last input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecoveredPattern at result
  cases result
  simp [State.emit]

/-- Every successful auxiliary pattern recovery retains a diagnostic,
including success at a pattern boundary or the active window end. -/
theorem recoverPatternAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : Pattern},
      recoverPatternAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverPatternAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverPatternAux at recovered
      split at recovered
      · exact finishRecoveredPattern_diagnostics_ne_nil_onSuccess first last
          recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecoveredPattern_diagnostics_ne_nil_onSuccess first
              last recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

end Solcore.Syntax.Parser.PatternInternals

namespace Solcore.Syntax.Parser

/-- A diagnostic-free public pattern-layer success is exactly the unchanged
successful result of its non-recovering Core pattern parser. -/
theorem patternCore_of_diagnosticFree_success
    (nested : Parser Pattern) (expression : Parser Expr)
    {input next : State} {value : Pattern}
    (result : patternLayer nested expression input = .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    PatternInternals.patternCore nested expression input = .ok value next := by
  unfold patternLayer at result
  cases coreResult : PatternInternals.patternCore nested expression input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if PatternInternals.isPatternBoundary rewound then
          .reject failure rewound
        else
          match rewound.advance? with
          | some (token, afterToken) =>
              PatternInternals.recoverPatternAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic)
          | none => .reject failure rewound) = .ok value next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none =>
            simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            exact False.elim
              (PatternInternals.recoverPatternAux_diagnostics_ne_nil_onSuccess
                token.span token.span (afterToken.remainingCount + 1) result
                  diagnosticFree)
  | invariant error =>
      simp [coreResult] at result

/-- Diagnostic reflection for the recovering public pattern layer reduces to
diagnostic reflection for its non-recovering Core parser. -/
theorem patternLayer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Pattern) (expression : Parser Expr)
    (coreReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (PatternInternals.patternCore nested expression)) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (patternLayer nested expression) := by
  intro input value next result diagnosticFree
  exact coreReflects input value next
    (patternCore_of_diagnosticFree_success nested expression result
      diagnosticFree)
    diagnosticFree

end Solcore.Syntax.Parser
