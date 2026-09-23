import Solcore.Frontend.LocalReference
import Solcore.Resolved.Typing
import Solcore.Resolved.FreshIdentity
import Solcore.Frontend.LocalName
import Solcore.Resolved.Renaming
import Solcore.Frontend.LocalOwnerRenaming

/-! Ordered type-only local inputs share identities between name resolution
and typing. They contain neither runtime values nor inhabitation evidence. -/

set_option autoImplicit false

namespace Solcore.Frontend

structure LocalTypeBinding where
  name : String
  id : Resolved.LocalId
  type : Core.Ty

structure LocalTypeInputs where
  bindings : List LocalTypeBinding
  ids_nodup : (bindings.map (·.id)).Nodup

namespace LocalTypeInputs

def ids (inputs : LocalTypeInputs) : List Resolved.LocalId :=
  inputs.bindings.map (·.id)

def names (inputs : LocalTypeInputs) : LocalNameTable :=
  inputs.bindings.map fun binding => (binding.name, binding.id)

def context (inputs : LocalTypeInputs) : Resolved.Context :=
  inputs.bindings.map fun binding => (binding.id, binding.type)

def empty : LocalTypeInputs := ⟨[], by simp⟩

/-- This explicit construction introduces no source-level binding policy. -/
def bindFresh (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) : LocalTypeInputs where
  bindings := { name, id := Resolved.freshLocalId owner inputs.ids, type } :: inputs.bindings
  ids_nodup := by
    change (Resolved.freshLocalId owner inputs.ids :: inputs.ids).Nodup
    exact List.nodup_cons.mpr
      ⟨Resolved.freshLocalId_not_mem owner inputs.ids, inputs.ids_nodup⟩

end LocalTypeInputs

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.LocalTypeInputsProperties`
-/

/-! Type-only inputs expose aligned static projections and fresh-binding laws,
without requiring or constructing a runtime environment. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalTypeInputs

@[simp] theorem context_ids (inputs : LocalTypeInputs) :
    Resolved.LocalScope.ids inputs.context = inputs.ids := by
  simp [context, ids, Resolved.LocalScope.ids, List.map_map]

@[simp] theorem names_ids (inputs : LocalTypeInputs) :
    inputs.names.map Prod.snd = inputs.ids := by
  simp only [names, ids, List.map_map, Function.comp_def]

@[simp] theorem empty_ids : empty.ids = [] := rfl

@[simp] theorem empty_names : empty.names = [] := rfl

@[simp] theorem empty_context : empty.context = [] := rfl

theorem bindFresh_bindings (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).bindings =
      { name, id := Resolved.freshLocalId owner inputs.ids, type } :: inputs.bindings := rfl

@[simp] theorem bindFresh_ids (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).ids =
      Resolved.freshLocalId owner inputs.ids :: inputs.ids := rfl

@[simp] theorem bindFresh_names (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).names =
      (name, Resolved.freshLocalId owner inputs.ids) :: inputs.names := rfl

@[simp] theorem bindFresh_context (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).context =
      (Resolved.freshLocalId owner inputs.ids, type) :: inputs.context := rfl

theorem bindFresh_id_fresh (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId) :
    Resolved.freshLocalId owner inputs.ids ∉ inputs.ids :=
  Resolved.freshLocalId_not_mem owner inputs.ids

end Solcore.Frontend.LocalTypeInputs

/-!
## Consolidated module: `Solcore.Frontend.LocalTypeInputsRenaming`
-/

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

/-!
## Consolidated module: `Solcore.Frontend.LocalTypeInputsOwnerProperties`
-/

/-! Value-free fresh binding commutes with injective owner-only relabeling
for arbitrary input scopes, without an extra fresh-index assumption. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalTypeInputs

theorem bindFresh_mapOwner (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective) =
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).bindFresh (mapping owner) name type := by
  have sameFresh : Resolved.freshLocalId (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).ids =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner inputs.ids) := by
    rw [mapIds_ids]
    exact Resolved.freshLocalId_map_owner mapping injective owner inputs.ids
  cases inputs
  simp only [mapIds, bindFresh, List.map_cons, LocalTypeBinding.mapIds, LocalTypeInputs.mk.injEq]
  congr 2
  exact sameFresh.symm

end Solcore.Frontend.LocalTypeInputs
