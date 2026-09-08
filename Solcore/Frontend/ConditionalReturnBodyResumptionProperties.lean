import Solcore.Frontend.ConditionalReturnBodyRunnerProperties
import Solcore.Core.FuelResumptionProperties

/-! Resume only the actual suspended state, with its pending conditional or arm
frames intact. Elaboration remains unchanged across every execution chunk. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ConditionalReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : ConditionalReturnBodyEvaluatesWithCost table environment initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateConditionalReturnBody? table context body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runConditionalReturnBody?_resume
    {inputs : LocalInputs} {body : Syntax.Block} {spent : Nat} {store : Core.Store}
    {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runConditionalReturnBody? spent body store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runConditionalReturnBody? (spent + additional) body store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runConditionalReturnBody?_eq_some_iff.mp exhausted
  exact runConditionalReturnBody?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend
