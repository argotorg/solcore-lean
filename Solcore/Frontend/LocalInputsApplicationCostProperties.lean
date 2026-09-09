import Solcore.Frontend.LocalInputsApplicationProperties
import Solcore.Core.FuelResumptionProperties

/-! Exact actual costs require whole-call typing. Resumption instead starts
from the genuine checked exhaustion result and retains every runtime outcome. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem runApplication?_done_iff_of_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType inputs.names inputs.context source type)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment
      initialStore source value finalStore cost) :
    inputs.runApplication? fuel source initialStore = some (type, .done value finalStore) ↔
      cost ≤ fuel := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  have checked : inputs.checkApplication? source = some (core, type) := elaboration.complete
  have path := evaluation.toSteps elaboration inputs.sameIds
  simpa [runApplication?, checked] using path.runStateful_done_iff (fuel := fuel)

theorem runApplication?_outOfFuel_iff_of_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalFunctionApplicationHasType inputs.names inputs.context source type)
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost fuel : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment
      initialStore source value finalStore cost) :
    (∃ checkpoint, inputs.runApplication? fuel source initialStore =
      some (type, .outOfFuel checkpoint)) ↔ fuel < cost := by
  obtain ⟨core, elaboration⟩ := typing.elaborates_exact
  have checked : inputs.checkApplication? source = some (core, type) := elaboration.complete
  have path := evaluation.toSteps elaboration inputs.sameIds
  simpa [runApplication?, checked] using path.runStateful_outOfFuel_iff (fuel := fuel)

theorem runApplication?_done_iff_typed_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {type : Core.Ty}
    {initialStore finalStore : Core.Store} {value : Core.Value} {fuel : Nat} :
    inputs.runApplication? fuel source initialStore = some (type, .done value finalStore) ↔
      LocalFunctionApplicationHasType inputs.names inputs.context source type ∧
        ∃ cost, LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment
          initialStore source value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro completed
    obtain ⟨core, checked, run⟩ := runApplication?_eq_some_iff.mp completed
    have elaboration := checkApplication?_iff_elaborates.mp checked
    obtain ⟨cost, enough, path⟩ := Core.runStateful_sound run
    exact ⟨elaboration.hasType, cost,
      (elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr path, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    exact (runApplication?_done_iff_of_cost typing evaluation).mpr enough

/-- The successful checker is recovered from the actual exhausted result;
no extra caller-supplied typing or replacement checkpoint is needed. -/
theorem runApplication?_residual_of_outOfFuel
    {inputs : LocalInputs} {source : Syntax.Expr}
    {initialStore finalStore : Core.Store} {value : Core.Value} {cost : Nat}
    (evaluation : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment
      initialStore source value finalStore cost)
    {type : Core.Ty} {spent : Nat} {checkpoint : Core.State}
    (exhausted : inputs.runApplication? spent source initialStore =
      some (type, .outOfFuel checkpoint)) :
    spent < cost ∧ Core.Steps (cost - spent) checkpoint (Core.State.final value finalStore) := by
  obtain ⟨core, checked, stopped⟩ := runApplication?_eq_some_iff.mp exhausted
  have elaboration := checkApplication?_iff_elaborates.mp checked
  exact (evaluation.toSteps elaboration inputs.sameIds).residual_of_outOfFuel stopped

/-- Preserve the same static tag and the complete resumed result, including
faults or further exhaustion. This is not a restart of the source expression. -/
theorem runApplication?_resume
    {inputs : LocalInputs} {source : Syntax.Expr} {store : Core.Store}
    {type : Core.Ty} {spent : Nat} {checkpoint : Core.State}
    (exhausted : inputs.runApplication? spent source store = some (type, .outOfFuel checkpoint))
    (additional : Nat) :
    inputs.runApplication? (spent + additional) source store =
      some (type, Core.runStateful additional checkpoint) := by
  obtain ⟨core, checked, stopped⟩ := runApplication?_eq_some_iff.mp exhausted
  exact runApplication?_eq_some_iff.mpr
    ⟨core, checked, (Core.runStateful_resume stopped additional).symm⟩

end Solcore.Frontend.LocalInputs
