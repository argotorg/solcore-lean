import Solcore.Frontend.LocalApplicationReturnBodyProperties
import Solcore.Frontend.LocalApplicationReturnBodyEvaluationProperties
import Solcore.Frontend.LocalInputsApplicationCostProperties

/-! Singleton wrapping preserves the child's entire checked result at every
fuel and store. Runtime-world and saved-state laws can be reused through this
equality without rebuilding inputs, frames, captures or stores. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkApplicationReturnBody?_return (inputs : LocalInputs)
    (blockSpan returnSpan : Syntax.SourceSpan) (source : Syntax.Expr) :
    inputs.checkApplicationReturnBody? ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ =
      inputs.checkApplication? source := rfl

theorem runApplicationReturnBody?_return (inputs : LocalInputs) (fuel : Nat)
    (blockSpan returnSpan : Syntax.SourceSpan) (source : Syntax.Expr) (store : Core.Store) :
    inputs.runApplicationReturnBody? fuel ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩ store =
      inputs.runApplication? fuel source store := rfl

theorem checkApplicationReturnBody?_iff_elaborates
    {inputs : LocalInputs} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty} :
    inputs.checkApplicationReturnBody? body = some (core, type) ↔
      LocalApplicationReturnBodyElaborates inputs.names inputs.context body core type :=
  elaborateLocalApplicationReturnBody?_iff

theorem runApplicationReturnBody?_eq_some_iff
    {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat} {store : Core.Store}
    {type : Core.Ty} {result : Core.StatefulRunResult} :
    inputs.runApplicationReturnBody? fuel body store = some (type, result) ↔
      ∃ core, inputs.checkApplicationReturnBody? body = some (core, type) ∧
        Core.runStateful fuel (Core.State.initial core
          (Resolved.LocalScope.values inputs.environment) store) = result := by
  simp only [runApplicationReturnBody?, bind, Option.bind_eq_some_iff, pure]
  constructor
  · rintro ⟨⟨core, actualType⟩, checked, same⟩
    cases same
    exact ⟨core, checked, rfl⟩
  · rintro ⟨core, checked, same⟩
    exact ⟨(core, type), checked, by simp only [same]⟩

theorem runApplicationReturnBody?_eq_none_iff
    {inputs : LocalInputs} {body : Syntax.Block} (fuel : Nat) (store : Core.Store) :
    inputs.runApplicationReturnBody? fuel body store = none ↔
      inputs.checkApplicationReturnBody? body = none := by
  cases checked : inputs.checkApplicationReturnBody? body with
  | none => simp [runApplicationReturnBody?, checked]
  | some pair => cases pair; simp [runApplicationReturnBody?, checked]

/-- Fixed-fuel completion requires whole-body typing and an actual successful
cost within that fuel. Raw selected-path success alone does not open the gate. -/
theorem runApplicationReturnBody?_done_iff_typed_cost
    {inputs : LocalInputs} {body : Syntax.Block} {fuel : Nat}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} :
    inputs.runApplicationReturnBody? fuel body initialStore = some (type, .done value finalStore) ↔
      LocalApplicationReturnBodyHasType inputs.names inputs.context body type ∧
        ∃ cost, LocalApplicationReturnBodyEvaluatesWithCost inputs.names inputs.environment
          initialStore body value finalStore cost ∧ cost ≤ fuel := by
  constructor
  · intro done
    obtain ⟨core, checked, execution⟩ := runApplicationReturnBody?_eq_some_iff.mp done
    have elaboration := checkApplicationReturnBody?_iff_elaborates.mp checked
    obtain ⟨cost, enough, path⟩ := Core.runStateful_sound execution
    exact ⟨elaboration.hasType, cost,
      (elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr path, enough⟩
  · rintro ⟨typing, cost, evaluation, enough⟩
    obtain ⟨core, elaboration⟩ := typing.elaborates_exact
    have path := evaluation.toStepsWithContinuation elaboration inputs.sameIds []
    exact runApplicationReturnBody?_eq_some_iff.mpr
      ⟨core, checkApplicationReturnBody?_iff_elaborates.mpr elaboration,
        path.runStateful_done_iff.mpr enough⟩

end Solcore.Frontend.LocalInputs
