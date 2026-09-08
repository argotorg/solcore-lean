import Solcore.Frontend.LocalInputsExtensionSemantics
import Solcore.Frontend.LocalInputsExecutionProperties
import Solcore.Resolved.ScopeExtensionProperties

/-! Unused-name insertion shifts free Core positions while preserving the
checked type, failure boundary, and completed value/store observations. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem AvoidsLocalName.check_bindFresh_complete {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType)
    {core : Core.Expr} {type : Core.Ty} (accepted : inputs.check? source = some (core, type)) :
    (inputs.bindFresh owner name newType newValue valueTyped).check? source =
      some (core.weakenAt 0, type) := by
  obtain ⟨resolved, resolution, lowered, typing⟩ := elaborateLocalExpression?_sound accepted
  have fresh : Resolved.freshLocalId owner inputs.ids ∉ Resolved.LocalScope.ids inputs.context := by
    simpa only [inputs.context_ids] using inputs.bindFresh_id_fresh owner
  exact elaborateLocalExpression?_complete
    (avoids.resolves_cons_iff.mpr resolution) (lowered.weaken_fresh fresh)
    (typing.weaken_fresh fresh newType)

/-- Exact checking agreement includes unresolved and ill-typed failures. Only
free Core indices shift; the source expression and assigned type are unchanged. -/
theorem AvoidsLocalName.check_bindFresh_eq {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType) :
    (inputs.bindFresh owner name newType newValue valueTyped).check? source =
      (inputs.check? source).map (fun result => (result.1.weakenAt 0, result.2)) := by
  cases accepted : inputs.check? source with
  | none =>
      have noOldType := elaborateLocalExpression?_eq_none_iff.mp accepted
      have newRejected : (inputs.bindFresh owner name newType newValue valueTyped).check? source = none :=
        elaborateLocalExpression?_eq_none_iff.mpr (by
          rintro ⟨type, typing⟩
          exact noOldType ⟨type,
            (avoids.bindFresh_hasType_iff inputs owner newType newValue valueTyped).mp typing⟩)
      simpa only [Option.map_none] using newRejected
  | some result =>
      rcases result with ⟨core, type⟩
      exact avoids.check_bindFresh_complete inputs owner newType newValue valueTyped accepted

/-- Completed runs agree on type, value, and both stores. Fuel bounds may be
witnessed separately; this law does not equate suspended Core states. -/
theorem AvoidsLocalName.bindFresh_run_done_iff {name : String} {source : Syntax.Expr}
    (avoids : AvoidsLocalName name source) (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (newType : Core.Ty) (newValue : Core.Value) (valueTyped : Core.ValueHasType newValue newType)
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} :
    (∃ fuel, (inputs.bindFresh owner name newType newValue valueTyped).run? fuel source initialStore =
      some (type, .done value finalStore)) ↔
      ∃ fuel, inputs.run? fuel source initialStore = some (type, .done value finalStore) := by
  rw [LocalInputs.run?_done_iff_typed_evaluation, LocalInputs.run?_done_iff_typed_evaluation]
  exact and_congr (avoids.bindFresh_hasType_iff inputs owner newType newValue valueTyped)
    (avoids.bindFresh_evaluates_iff inputs owner newType newValue valueTyped)

end Solcore.Frontend
