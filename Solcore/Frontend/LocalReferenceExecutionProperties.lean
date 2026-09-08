import Solcore.Frontend.LocalReferenceElaborationProperties
import Solcore.Frontend.LocalReferenceEvaluation
import Solcore.Core.Safety

set_option autoImplicit false

namespace Solcore.Frontend

/-- A checked source reference and its Core variable have exactly the same
evaluation. Context and environment must agree on identity order, including duplicates. -/
theorem elaborateLocalReference?_evaluates_iff
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    {initialStore finalStore : Core.Store} {value : Core.Value}
    (accepted : elaborateLocalReference? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context) :
    Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore ↔
      LocalReferenceEvaluates table environment source value ∧ finalStore = initialStore := by
  obtain ⟨id, index, reference, indexed, _, rfl⟩ := elaborateLocalReference?_sound accepted
  have envIndex : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index := by
    rw [sameIds]
    exact indexed
  constructor
  · intro evaluation
    cases evaluation with
    | var atValue =>
        exact ⟨.reference reference (Resolved.LocalScope.lookup_of_indexed envIndex atValue), rfl⟩
  · rintro ⟨evaluation, rfl⟩
    cases evaluation with
    | reference actual found =>
        cases reference.id_unique actual
        exact .var ((Resolved.LocalScope.lookup_iff_getElem? envIndex).mp found)

/-- An independently typed reference has a value in any matching typed environment. -/
theorem LocalReferenceHasType.evaluates
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty}
    (typing : LocalReferenceHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    ∃ value, LocalReferenceEvaluates table environment source value ∧ Core.ValueHasType value type := by
  cases typing with
  | resolved reference found =>
      rename_i id
      obtain ⟨index, indexed, atType⟩ := found.indexed
      obtain ⟨value, atValue, valueTyped⟩ := environmentTyped.lookup atType
      have envIndex : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index := by
        rw [sameIds]
        exact indexed
      exact ⟨value, .reference reference
        (Resolved.LocalScope.lookup_of_indexed envIndex atValue), valueTyped⟩

theorem LocalReferenceEvaluates.preserves_type
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {type : Core.Ty} {value : Core.Value}
    (evaluation : LocalReferenceEvaluates table environment source value)
    (typing : LocalReferenceHasType table context source type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context)) :
    Core.ValueHasType value type := by
  obtain ⟨other, evaluated, valueTyped⟩ := typing.evaluates sameIds environmentTyped
  cases evaluation.deterministic evaluated
  exact valueTyped

/-- Checked grouping has no execution overhead: zero fuel retains the initial
state, and every positive Core fuel returns the independently selected value. -/
theorem elaborateLocalReference?_exact_run
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty} {value : Core.Value}
    (accepted : elaborateLocalReference? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (evaluation : LocalReferenceEvaluates table environment source value)
    (store : Core.Store) :
    Core.runStateful 0 (Core.State.initial core (Resolved.LocalScope.values environment) store) =
      .outOfFuel (Core.State.initial core (Resolved.LocalScope.values environment) store) ∧
    ∀ fuel, Core.runStateful (fuel + 1)
      (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  have coreEvaluation := (elaborateLocalReference?_evaluates_iff accepted sameIds).mpr
    (show LocalReferenceEvaluates table environment source value ∧ store = store from ⟨evaluation, rfl⟩)
  obtain ⟨_, _, _, _, _, rfl⟩ := elaborateLocalReference?_sound accepted
  cases coreEvaluation with
  | var atValue =>
      constructor
      · simp [Core.runStateful, Core.State.initial, Core.advance, atValue]
      · intro fuel
        simp [Core.runStateful, Core.State.initial, Core.advance, atValue]

/-- The checked endpoint has a typed, store-preserving execution for every positive fuel. -/
theorem elaborateLocalReference?_typed_execution
    {table : LocalNameTable} {context : Resolved.Context} {environment : Resolved.Environment}
    {source : Syntax.Expr} {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateLocalReference? table context source = some (core, type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values context))
    (store : Core.Store) :
    ∃ value, LocalReferenceEvaluates table environment source value ∧
      Core.ValueHasType value type ∧
      ∀ fuel, Core.runStateful (fuel + 1)
        (Core.State.initial core (Resolved.LocalScope.values environment) store) = .done value store := by
  have typing := localReferenceHasType_iff_elaborates.mpr ⟨core, accepted⟩
  obtain ⟨value, evaluation, valueTyped⟩ := typing.evaluates sameIds environmentTyped
  exact ⟨value, evaluation, valueTyped,
    (elaborateLocalReference?_exact_run accepted sameIds evaluation store).2⟩

end Solcore.Frontend
