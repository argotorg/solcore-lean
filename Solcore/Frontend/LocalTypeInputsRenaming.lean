import Solcore.Frontend.LocalTypeInputs
import Solcore.Frontend.LocalNameRenaming
import Solcore.Resolved.RenamingProperties

/-! Relabel explicit input identities without changing row order, spelling,
or type. Injectivity preserves the bundle's unique-ID invariant. -/

set_option autoImplicit false

namespace Solcore.Frontend

def LocalTypeBinding.mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (binding : LocalTypeBinding) : LocalTypeBinding :=
  { binding with id := mapping binding.id }

@[simp] theorem LocalTypeBinding.mapIds_id (binding : LocalTypeBinding) :
    binding.mapIds _root_.id = binding := by cases binding; rfl

theorem LocalTypeBinding.mapIds_comp (binding : LocalTypeBinding)
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

namespace LocalTypeInputs

def mapIds (inputs : LocalTypeInputs) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) : LocalTypeInputs where
  bindings := inputs.bindings.map (LocalTypeBinding.mapIds mapping)
  ids_nodup := by
    simpa [LocalTypeBinding.mapIds, List.map_map, Function.comp_def] using
      nodup_map_injective mapping injective inputs.ids_nodup

@[simp] theorem mapIds_bindings (inputs : LocalTypeInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).bindings =
      inputs.bindings.map (LocalTypeBinding.mapIds mapping) := rfl

@[simp] theorem mapIds_ids (inputs : LocalTypeInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).ids = inputs.ids.map mapping := by
  simp [ids, mapIds, LocalTypeBinding.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_names (inputs : LocalTypeInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).names = LocalNameTable.mapIds mapping inputs.names := by
  simp [names, mapIds, LocalTypeBinding.mapIds, LocalNameTable.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_context (inputs : LocalTypeInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).context = Resolved.LocalScope.mapIds mapping inputs.context := by
  simp [context, mapIds, LocalTypeBinding.mapIds, Resolved.LocalScope.mapIds, List.map_map, Function.comp_def]

@[simp] theorem mapIds_id (inputs : LocalTypeInputs) :
    inputs.mapIds id (fun _ _ same => same) = inputs := by
  cases inputs
  simp [mapIds, show LocalTypeBinding.mapIds id = id from funext LocalTypeBinding.mapIds_id]

theorem mapIds_comp (inputs : LocalTypeInputs) (first second : Resolved.LocalId → Resolved.LocalId)
    (firstInjective : Function.Injective first) (secondInjective : Function.Injective second) :
    (inputs.mapIds first firstInjective).mapIds second secondInjective =
      inputs.mapIds (second ∘ first) (secondInjective.comp firstInjective) := by
  cases inputs
  simp [mapIds, List.map_map, Function.comp_def, LocalTypeBinding.mapIds_comp]

end LocalTypeInputs

end Solcore.Frontend
