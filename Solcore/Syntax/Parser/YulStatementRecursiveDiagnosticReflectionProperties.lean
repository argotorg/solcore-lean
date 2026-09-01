import Solcore.Syntax.Parser.YulStatementCoreDiagnosticReflectionProperties

/-! Diagnostic reflection for recursive and public inline-Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every explicit recursive fuel layer reflects diagnostic freedom through
its preceding nested layer. -/
theorem yulStatementWithFuel_reflectsDiagnosticFreeOnSuccess :
    ∀ fuel,
      Parser.ReflectsDiagnosticFreeOnSuccess (yulStatementWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input value output result diagnosticFree
      simp [yulStatementWithFuel] at result
  | succ fuel inductionHypothesis =>
      simpa only [yulStatementWithFuel] using
        yulStatementLayer_reflectsDiagnosticFreeOnSuccess_of_core
          (yulStatementWithFuel fuel) inductionHypothesis

/-- The public remaining-token fuel selection also reflects diagnostic
freedom. -/
theorem yulStatement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulStatement := by
  intro input value output result diagnosticFree
  unfold yulStatement at result
  exact yulStatementWithFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 1) input value output result diagnosticFree

end Solcore.Syntax.Parser
