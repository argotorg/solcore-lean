import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Yul.Statement

/-!
Diagnostic commitments at inline-Yul statement choice and recovery boundaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A diagnostic-free recognized-Yul choice success is the unchanged primary
success; fallback success after primary rejection commits that failure. -/
theorem recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
    (primary fallback : Parser YulStmt)
    {input next : State} {value : YulStmt}
    (result : recognizedYulStatementOrFallback primary fallback input =
      .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    primary input = .ok value next := by
  unfold recognizedYulStatementOrFallback at result
  cases primaryResult : primary input with
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState =>
          simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          cases result
          simp [State.emit] at diagnosticFree
  | invariant error => simp [primaryResult] at result

theorem recognizedYulStatementOrFallback_reflectsDiagnosticFreeOnSuccess
    (primary fallback : Parser YulStmt)
    (primaryReflects : Parser.ReflectsDiagnosticFreeOnSuccess primary) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (recognizedYulStatementOrFallback primary fallback) := by
  intro input value next result diagnosticFree
  exact primaryReflects input value next
    (recognizedYulStatementOrFallback_primary_of_diagnosticFree_success
      primary fallback result diagnosticFree)
    diagnosticFree

/-- Finishing Yul-statement recovery always commits its diagnostic. -/
theorem finishRecoveredYulStatement_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) {input next : State} {value : YulStmt}
    (result : finishRecoveredYulStatement first last input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold finishRecoveredYulStatement at result
  cases result
  simp [State.emit]

/-- Every successful Yul-statement recovery scan retains a diagnostic. -/
theorem recoverYulStatementAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : YulStmt},
      recoverYulStatementAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverYulStatementAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverYulStatementAux at recovered
      split at recovered
      · exact finishRecoveredYulStatement_diagnostics_ne_nil_onSuccess
          first last recovered
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            exact finishRecoveredYulStatement_diagnostics_ne_nil_onSuccess
              first last recovered
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- A diagnostic-free recovering Yul-statement layer success is exactly its
unchanged non-recovering terminated-statement success. -/
theorem yulStatementTerminated_of_diagnosticFree_layer_success
    (nested : Parser YulStmt) {input next : State} {value : YulStmt}
    (result : yulStatementLayer nested input = .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    yulStatementTerminated nested input = .ok value next := by
  unfold yulStatementLayer at result
  cases coreResult : yulStatementTerminated nested input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      rfl
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .rightBrace then
          .reject failure rewound
        else
          match rewound.advance? with
          | some (token, afterToken) =>
              recoverYulStatementAux token.span token.span
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
              (recoverYulStatementAux_diagnostics_ne_nil_onSuccess
                token.span token.span (afterToken.remainingCount + 1) result
                  diagnosticFree)
  | invariant error => simp [coreResult] at result

theorem yulStatementLayer_reflectsDiagnosticFreeOnSuccess
    (nested : Parser YulStmt)
    (terminatedReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (yulStatementTerminated nested)) :
    Parser.ReflectsDiagnosticFreeOnSuccess (yulStatementLayer nested) := by
  intro input value next result diagnosticFree
  exact terminatedReflects input value next
    (yulStatementTerminated_of_diagnosticFree_layer_success nested result
      diagnosticFree)
    diagnosticFree

end Solcore.Syntax.Parser
