import Solcore.Frontend.LocalInputs

/-! Projection alignment and fresh-input construction are structural. These
laws require no caller-supplied synchronization of names, types, and values. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

@[simp] theorem context_ids (inputs : LocalInputs) :
    Resolved.LocalScope.ids inputs.context = inputs.ids := by
  simp [context, ids, Resolved.LocalScope.ids, List.map_map]

@[simp] theorem environment_ids (inputs : LocalInputs) :
    Resolved.LocalScope.ids inputs.environment = inputs.ids := by
  simp [environment, ids, Resolved.LocalScope.ids, List.map_map]

theorem sameIds (inputs : LocalInputs) :
    Resolved.LocalScope.ids inputs.environment =
      Resolved.LocalScope.ids inputs.context :=
  (environment_ids inputs).trans (context_ids inputs).symm

theorem environmentTyped (inputs : LocalInputs) :
    Core.EnvironmentHasTypes (Resolved.LocalScope.values inputs.environment)
      (Resolved.LocalScope.values inputs.context) := by
  have typed : Core.EnvironmentHasTypes
      (inputs.bindings.map (·.value)) (inputs.bindings.map (·.type)) := by
    induction inputs.bindings with
    | nil => exact .nil
    | cons binding rest ih => exact .cons binding.valueTyped ih
  simpa [environment, context, Resolved.LocalScope.values, List.map_map, Function.comp_def] using typed

@[simp] theorem empty_ids : empty.ids = [] := rfl

@[simp] theorem empty_names : empty.names = [] := rfl

@[simp] theorem empty_context : empty.context = [] := rfl

@[simp] theorem empty_environment : empty.environment = [] := rfl

theorem bindFresh_bindings (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).bindings =
      { name, id := Resolved.freshLocalId owner inputs.ids, type, value, valueTyped } ::
        inputs.bindings := rfl

@[simp] theorem bindFresh_ids (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).ids =
      Resolved.freshLocalId owner inputs.ids :: inputs.ids := rfl

@[simp] theorem bindFresh_names (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).names =
      (name, Resolved.freshLocalId owner inputs.ids) :: inputs.names := rfl

@[simp] theorem bindFresh_context (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).context =
      (Resolved.freshLocalId owner inputs.ids, type) :: inputs.context := rfl

@[simp] theorem bindFresh_environment (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).environment =
      (Resolved.freshLocalId owner inputs.ids, value) :: inputs.environment := rfl

/-- Freshness is relative to the supplied inputs, not a global allocation claim. -/
theorem bindFresh_id_fresh (inputs : LocalInputs) (owner : Resolved.DeclarationId) :
    Resolved.freshLocalId owner inputs.ids ∉ inputs.ids :=
  Resolved.freshLocalId_not_mem owner inputs.ids

end Solcore.Frontend.LocalInputs
