import Solcore.Frontend.TypedLetReturnBodyRunnerProperties
import Solcore.Core.FuelResumptionProperties

/-! A genuine exhausted state retains every pending let frame, captured
environment and actual value. Exact residual costs use a closed final path;
arbitrary continuation endpoints are not treated as completed body runs. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyEvaluatesWithCost.checked_residual_of_outOfFuel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateTypedLetReturnBody? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runTypedLetReturnBody?_resume
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalInputs}
    {body : Syntax.Block} {spent : Nat} {store : Core.Store} {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runTypedLetReturnBody? types owner spent body store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runTypedLetReturnBody? types owner (spent + additional) body store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runTypedLetReturnBody?_eq_some_iff.mp exhausted
  exact runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend
