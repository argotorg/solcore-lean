import Solcore.Frontend.LocalExpressionCostExecutionProperties
import Solcore.Frontend.LocalExpressionCostInvariance

/-! Same-fuel observations survive insertion of an unused typed input.
Completed type, value, and stores agree; exhausted states are deliberately
quantified separately because their Core indices and environments can differ. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Present exhaustion is exactly whole source typing together with a
successful independent cost larger than the supplied fuel. Check failure
cannot satisfy either side, even when a raw evaluation skips the bad branch. -/
theorem LocalInputs.run?_outOfFuel_iff_typed_cost
    {inputs : LocalInputs} {source : Syntax.Expr} {store : Core.Store}
    {type : Core.Ty} {fuel : Nat} :
    (∃ suspended, inputs.run? fuel source store = some (type, .outOfFuel suspended)) ↔
      LocalExpressionHasType inputs.names inputs.context source type ∧
      ∃ value cost, LocalExpressionEvaluatesWithCost inputs.names inputs.environment
        store source value store cost ∧ fuel < cost := by
  constructor
  · rintro ⟨suspended, exhausted⟩
    obtain ⟨core, checked, _⟩ := LocalInputs.run?_eq_some_iff.mp exhausted
    have typing := LocalInputs.check?_iff_hasType.mp ⟨core, checked⟩
    obtain ⟨value, cost, costed, _, boundaries⟩ := LocalInputs.typed_cost_execution typing store
    exact ⟨typing, value, cost, costed, (boundaries fuel).2.mp ⟨suspended, exhausted⟩⟩
  · rintro ⟨typing, value, cost, costed, short⟩
    obtain ⟨core, checked⟩ := LocalInputs.check?_iff_hasType.mpr typing
    obtain ⟨suspended, exhausted⟩ :=
      (costed.checked_runStateful_outOfFuel_iff checked inputs.sameIds).mpr short
    exact ⟨suspended, LocalInputs.run?_eq_some_iff.mpr ⟨core, checked, exhausted⟩⟩

/-- Unlike existential sufficient-fuel agreement, this law uses the very same
fuel on both sides and retains the completed type, value, and both stores. -/
theorem AvoidsLocalName.bindFresh_run_done_at_fuel_iff
    {name : String} {source : Syntax.Expr} (avoids : AvoidsLocalName name source)
    (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {fuel : Nat} :
    (inputs.bindFresh owner name newType newValue valueTyped).run? fuel source initialStore =
        some (type, .done value finalStore) ↔
      inputs.run? fuel source initialStore = some (type, .done value finalStore) := by
  rw [LocalInputs.run?_done_iff_typed_cost, LocalInputs.run?_done_iff_typed_cost]
  refine and_congr (avoids.bindFresh_hasType_iff inputs owner newType newValue valueTyped) ?_
  exact exists_congr fun _ =>
    and_congr (avoids.bindFresh_cost_iff inputs owner newType newValue valueTyped) Iff.rfl

/-- Only exhaustion presence is compared. The old and new suspended states
are separate witnesses, with no equality or shared-state premise. -/
theorem AvoidsLocalName.bindFresh_run_outOfFuel_iff
    {name : String} {source : Syntax.Expr} (avoids : AvoidsLocalName name source)
    (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType)
    {store : Core.Store} {type : Core.Ty} {fuel : Nat} :
    (∃ newSuspended, (inputs.bindFresh owner name newType newValue valueTyped).run? fuel source store =
        some (type, .outOfFuel newSuspended)) ↔
      ∃ oldSuspended, inputs.run? fuel source store = some (type, .outOfFuel oldSuspended) := by
  rw [LocalInputs.run?_outOfFuel_iff_typed_cost, LocalInputs.run?_outOfFuel_iff_typed_cost]
  refine and_congr (avoids.bindFresh_hasType_iff inputs owner newType newValue valueTyped) ?_
  exact exists_congr fun _ => exists_congr fun _ =>
    and_congr (avoids.bindFresh_cost_iff inputs owner newType newValue valueTyped) Iff.rfl

end Solcore.Frontend
