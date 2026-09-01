import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Yul.Expression

/-!
Diagnostic commitments at inline-Yul expression rejection and recovery
boundaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Consuming forbidden source-level Yul meta syntax always emits its
constraint diagnostic. -/
theorem rejectedMeta_diagnostics_ne_nil_onSuccess
    {input next : State} {value : YulExpr}
    (result : rejectedMeta input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold rejectedMeta at result
  cases found : input.peek? with
  | none => simp [found, rejectAt] at result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals simp [State.emit]

/-- Forbidden Yul meta syntax cannot have a diagnostic-free success. -/
theorem rejectedMeta_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess rejectedMeta := by
  intro input value next result diagnosticFree
  exact False.elim
    (rejectedMeta_diagnostics_ne_nil_onSuccess result diagnosticFree)

namespace YulExpressionInternals

/-- Finishing a recovered Yul expression always commits its recovery
diagnostic. -/
theorem finishRecovered_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) {input next : State} {value : YulExpr}
    (result : finishRecovered first last input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecovered at result
  cases result
  simp [State.emit]

/-- Every successful auxiliary Yul-expression recovery retains a diagnostic,
including success at a recovery boundary or at the active window end. -/
theorem recoverAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : YulExpr},
      recoverAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverAux at recovered
      split at recovered
      · exact finishRecovered_diagnostics_ne_nil_onSuccess first last
          recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecovered_diagnostics_ne_nil_onSuccess first last
              recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- A diagnostic-free public Yul-layer success is exactly the unchanged
successful result of its non-recovering core parser. -/
theorem layer_core_of_diagnosticFree_success
    (nested : Parser YulExpr) {input next : State} {value : YulExpr}
    (result : layer nested input = .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    yulExpressionCore nested input = .ok value next := by
  unfold layer at result
  cases coreResult : yulExpressionCore nested input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if isBoundary rewound then .reject failure rewound
        else
          match rewound.advance? with
          | some (token, afterToken) =>
              recoverAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic)
          | none => .reject failure rewound) = .ok value next at result
      split at result
      · contradiction
      · cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            exact False.elim
              (recoverAux_diagnostics_ne_nil_onSuccess token.span token.span
                (afterToken.remainingCount + 1) result diagnosticFree)
  | invariant error =>
      simp [coreResult] at result

/-- Diagnostic reflection for the recovering Yul layer reduces to diagnostic
reflection for its non-recovering core parser. -/
theorem layer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulExpr)
    (coreReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (yulExpressionCore nested)) :
    Parser.ReflectsDiagnosticFreeOnSuccess (layer nested) := by
  intro input value next result diagnosticFree
  exact coreReflects input value next
    (layer_core_of_diagnosticFree_success nested result diagnosticFree)
    diagnosticFree

end YulExpressionInternals

end Solcore.Syntax.Parser
