import Solcore.Frontend.LocalInputs
import Solcore.Frontend.LocalTypeInputsProperties

/-! Erase supplied values and their typing evidence while retaining the exact
ordered static rows. This direction requires no runtime-value reconstruction. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

def toTypeInputs (inputs : LocalInputs) : LocalTypeInputs where
  bindings := inputs.bindings.map fun binding =>
    { name := binding.name, id := binding.id, type := binding.type }
  ids_nodup := by
    simpa only [List.map_map, Function.comp_def] using inputs.ids_nodup

@[simp] theorem toTypeInputs_ids (inputs : LocalInputs) :
    inputs.toTypeInputs.ids = inputs.ids := by
  simp only [toTypeInputs, LocalTypeInputs.ids, ids, List.map_map, Function.comp_def]

@[simp] theorem toTypeInputs_names (inputs : LocalInputs) :
    inputs.toTypeInputs.names = inputs.names := by
  simp only [toTypeInputs, LocalTypeInputs.names, names, List.map_map, Function.comp_def]

@[simp] theorem toTypeInputs_context (inputs : LocalInputs) :
    inputs.toTypeInputs.context = inputs.context := by
  simp only [toTypeInputs, LocalTypeInputs.context, context, List.map_map, Function.comp_def]

@[simp] theorem toTypeInputs_empty : empty.toTypeInputs = LocalTypeInputs.empty := rfl

@[simp] theorem toTypeInputs_bindFresh (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (name : String) (type : Core.Ty) (value : Core.Value) (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).toTypeInputs =
      inputs.toTypeInputs.bindFresh owner name type := by
  cases inputs
  simp only [toTypeInputs, bindFresh, LocalTypeInputs.bindFresh, LocalTypeInputs.ids, ids,
    List.map_cons, List.map_map, Function.comp_def]

end Solcore.Frontend.LocalInputs
