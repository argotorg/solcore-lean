import Solcore.Frontend.LocalExpressionResumptionProperties
import Solcore.Frontend.ReturnBodyExecutionProperties

/-! A singleton return has no additional resumption transition. Actual exhausted
states retain their pending frames and the complete original checked body. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : ReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runReturnBody?_resume
    {inputs : LocalInputs} {body : Syntax.Block} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runReturnBody? spent body store = some (type, .outOfFuel checkpoint)) (additional : Nat) :
    inputs.runReturnBody? (spent + additional) body store = some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runReturnBody?_eq_some_iff.mp exhausted
  exact runReturnBody?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend
