import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Term

/-!
Diagnostic commitment at the recognized-statement fallback boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- A diagnostic-free success of recognized-statement choice is exactly the
unchanged success of the recognized primary branch.  A fallback success after
primary rejection necessarily commits the primary failure diagnostic. -/
theorem recognizedStatementOrFallback_primary_of_diagnosticFree_success
    (primary fallback : Parser Statement)
    {input next : State} {value : Statement}
    (result : recognizedStatementOrFallback primary fallback input =
      .ok value next)
    (diagnosticFree : next.diagnosticsRev = []) :
    primary input = .ok value next := by
  unfold recognizedStatementOrFallback at result
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

/-- Diagnostic reflection for recognized-statement choice reduces to the
primary parser on every diagnostic-free success. -/
theorem recognizedStatementOrFallback_reflectsDiagnosticFreeOnSuccess
    (primary fallback : Parser Statement)
    (primaryReflects : Parser.ReflectsDiagnosticFreeOnSuccess primary) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (recognizedStatementOrFallback primary fallback) := by
  intro input value next result diagnosticFree
  exact primaryReflects input value next
    (recognizedStatementOrFallback_primary_of_diagnosticFree_success
      primary fallback result diagnosticFree)
    diagnosticFree

end Solcore.Syntax.Parser.TermInternals
