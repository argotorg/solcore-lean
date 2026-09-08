import Solcore.Frontend.LocalInputs
import Solcore.Frontend.LocalNameRenaming
import Solcore.Resolved.RenamingProperties

/-! Relabel explicit input identities without changing row order, spelling,
type, or value. Injectivity preserves the bundle's unique-ID invariant. -/

set_option autoImplicit false

namespace Solcore.Frontend

def TypedLocalBinding.mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (binding : TypedLocalBinding) : TypedLocalBinding :=
  { binding with id := mapping binding.id }

@[simp] theorem TypedLocalBinding.mapIds_id (binding : TypedLocalBinding) :
    binding.mapIds _root_.id = binding := by cases binding; rfl

theorem TypedLocalBinding.mapIds_comp (binding : TypedLocalBinding)
    (first second : Resolved.LocalId → Resolved.LocalId) :
    (binding.mapIds first).mapIds second = binding.mapIds (second ∘ first) := rfl

private theorem nodup_map_injective {α β : Type} (mapping : α → β)
    (injective : Function.Injective mapping) {values : List α} (distinct : values.Nodup) :
    (values.map mapping).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons value rest ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
        exact absent (injective same ▸ originalMember)
      · exact ih tailDistinct

namespace LocalInputs

def mapIds (inputs : LocalInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) : LocalInputs where
  bindings := inputs.bindings.map (TypedLocalBinding.mapIds mapping)
  ids_nodup := by
    simpa [TypedLocalBinding.mapIds, List.map_map, Function.comp_def] using
      nodup_map_injective mapping injective inputs.ids_nodup

@[simp] theorem mapIds_bindings (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).bindings =
      inputs.bindings.map (TypedLocalBinding.mapIds mapping) := rfl

@[simp] theorem mapIds_ids (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).ids = inputs.ids.map mapping := by
  simp [ids, mapIds, TypedLocalBinding.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_names (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).names = LocalNameTable.mapIds mapping inputs.names := by
  simp [names, mapIds, TypedLocalBinding.mapIds, LocalNameTable.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_context (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).context = Resolved.LocalScope.mapIds mapping inputs.context := by
  simp [context, mapIds, TypedLocalBinding.mapIds, Resolved.LocalScope.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_environment (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).environment = Resolved.LocalScope.mapIds mapping inputs.environment := by
  simp [environment, mapIds, TypedLocalBinding.mapIds, Resolved.LocalScope.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_id (inputs : LocalInputs) :
    inputs.mapIds id (fun _ _ same => same) = inputs := by
  cases inputs
  simp [mapIds, show TypedLocalBinding.mapIds id = id from funext TypedLocalBinding.mapIds_id]

theorem mapIds_comp (inputs : LocalInputs) (first second : Resolved.LocalId → Resolved.LocalId)
    (firstInjective : Function.Injective first) (secondInjective : Function.Injective second) :
    (inputs.mapIds first firstInjective).mapIds second secondInjective =
      inputs.mapIds (second ∘ first) (secondInjective.comp firstInjective) := by
  cases inputs
  simp [mapIds, List.map_map, Function.comp_def, TypedLocalBinding.mapIds_comp]

end LocalInputs

end Solcore.Frontend
