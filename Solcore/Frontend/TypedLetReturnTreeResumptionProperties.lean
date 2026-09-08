import Solcore.Frontend.TypedLetReturnTreeRunnerProperties
import Solcore.Core.FuelResumptionProperties

/-! Genuine checkpoints retain selected branches, pending let frames and actual
captured values. Exact residual cost uses a closed final path, not an arbitrary
continuation endpoint or a reconstructed initial state. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeEvaluatesWithCost.checked_residual_of_outOfFuel
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {body : Syntax.Block} {value : Core.Value} {cost spent : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner inputs.names environment
      initialStore body value finalStore cost)
    {core : Core.Expr} {type : Core.Ty} {checkpoint : Core.State}
    (accepted : elaborateTypedLetReturnTree? types owner inputs body = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (exhausted : Core.runStateful spent (Core.State.initial core
      (Resolved.LocalScope.values environment) initialStore) = .outOfFuel checkpoint) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) :=
  (evaluation.checked_toSteps accepted sameIds).residual_of_outOfFuel exhausted

theorem LocalInputs.runTypedLetReturnTree?_resume
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalInputs}
    {body : Syntax.Block} {spent : Nat} {store : Core.Store} {type : Core.Ty} {checkpoint : Core.State}
    (exhausted : inputs.runTypedLetReturnTree? types owner spent body store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runTypedLetReturnTree? types owner (spent + additional) body store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, execution⟩ := runTypedLetReturnTree?_eq_some_iff.mp exhausted
  exact runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, checked, (Core.runStateful_resume execution additional).symm⟩

end Solcore.Frontend
