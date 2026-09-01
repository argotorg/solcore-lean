import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Expression.Atom

/-!
Diagnostic commitments at the public Core expression-atom recovery boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Finishing a recovered atom always commits its recovery diagnostic. -/
theorem finishRecoveredAtom_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) {input next : State} {value : Expr}
    (result : finishRecoveredAtom first last input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecoveredAtom at result
  cases result
  simp [State.emit]

/-- Every successful auxiliary atom recovery retains a diagnostic, including
success at a token boundary or at the active window end. -/
theorem recoverAtomAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : Expr},
      recoverAtomAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverAtomAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverAtomAux at recovered
      split at recovered
      · exact finishRecoveredAtom_diagnostics_ne_nil_onSuccess first last
          recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecoveredAtom_diagnostics_ne_nil_onSuccess first last
              recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- Every successful complete atom recovery commits a recovery diagnostic. -/
theorem recoverAtom_diagnostics_ne_nil_onSuccess
    {input next : State} {value : Expr}
    (recovered : recoverAtom input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverAtom at recovered
  cases advanced : input.advance? with
  | none =>
      simp [advanced, rejectAt] at recovered
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at recovered
      exact recoverAtomAux_diagnostics_ne_nil_onSuccess token.span token.span
        (afterToken.remainingCount + 1) recovered

end Solcore.Syntax.Parser.ExpressionAtomInternals

namespace Solcore.Syntax.Parser

/-- A diagnostic-free public atom success is exactly the unchanged successful
result of the non-recovering Core atom parser. -/
theorem expressionAtomCore_of_diagnosticFree_success
    (nested : Parser Expr) (block : Parser Block)
    {input next : State} {value : Expr}
    (result : expressionAtom nested block input = .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    ExpressionAtomInternals.expressionAtomCore nested block input =
      .ok value next := by
  unfold expressionAtom at result
  cases coreResult : ExpressionAtomInternals.expressionAtomCore nested block
      input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if ExpressionAtomInternals.isAtomBoundary rewound then
          .reject failure rewound
        else ExpressionAtomInternals.recoverAtom
          (rewound.emit failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · exact False.elim
          (ExpressionAtomInternals.recoverAtom_diagnostics_ne_nil_onSuccess
            result diagnosticFree)
  | invariant error =>
      simp [coreResult] at result

/-- Diagnostic reflection for the public recoverable atom parser reduces to
diagnostic reflection for its non-recovering Core branch. -/
theorem expressionAtom_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (coreReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (ExpressionAtomInternals.expressionAtomCore nested block)) :
    Parser.ReflectsDiagnosticFreeOnSuccess (expressionAtom nested block) := by
  intro input value next result diagnosticFree
  exact coreReflects input value next
    (expressionAtomCore_of_diagnosticFree_success nested block result
      diagnosticFree)
    diagnosticFree

end Solcore.Syntax.Parser
