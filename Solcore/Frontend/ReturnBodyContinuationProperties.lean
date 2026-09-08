import Solcore.Frontend.ReturnBodyExecutionProperties

/-! Return wrappers preserve exact paths under any still-pending continuation.
The continuation is retained, not executed or discarded at the endpoint. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyEvaluatesWithCost.checked_toStepsWithContinuation
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (continuation : List Core.Frame) :
    Core.Steps cost
      ⟨.eval core (Resolved.LocalScope.values environment), continuation, initialStore⟩
      ⟨.ret value, continuation, finalStore⟩ := by
  cases evaluation with
  | bare =>
      simp only [elaborateReturnBody?, Option.some.injEq, Prod.mk.injEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact .cons .unit .refl
  | expression child =>
      obtain ⟨resolved, resolution, lowered, _⟩ := elaborateLocalExpression?_sound accepted
      have runtimeLowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core := by
        rw [sameIds]
        exact lowered
      exact child.toStepsWithContinuation resolution runtimeLowered continuation

end Solcore.Frontend
