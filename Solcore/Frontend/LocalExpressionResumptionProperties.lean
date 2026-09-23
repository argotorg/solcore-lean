import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.LocalFunctionApplication

/-! A source cost determines the exact remaining path after genuine Core fuel
exhaustion. Whole checking is preserved at the executable local-input boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem LocalExpressionEvaluatesWithCost.residual_of_outOfFuel
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost spent : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost)
    {resolved : Resolved.Expr} {core : Core.Expr} {checkpoint : Core.State}
    (resolution : ResolvesLocalExpression table source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.toSteps resolution lowered).residual_of_outOfFuel exhausted

theorem LocalExpressionEvaluatesWithCost.checked_residual_of_outOfFuel
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {source : Syntax.Expr} {value : Core.Value} {cost spent : Nat}
    (evaluation : LocalExpressionEvaluatesWithCost table environment initialStore source value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateLocalExpression? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

/-- Reuse the checked expression and actual checkpoint; no source re-entry
state or replacement continuation is constructed. -/
theorem LocalInputs.run?_resume
    {inputs : LocalInputs} {source : Syntax.Expr} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.run? spent source store = some (type, .outOfFuel checkpoint)) (additional : Nat) :
    inputs.run? (spent + additional) source store = some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := run?_eq_some_iff.mp exhausted
  exact run?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend
