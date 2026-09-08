import Solcore.Frontend.LocalTypeInputs

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
