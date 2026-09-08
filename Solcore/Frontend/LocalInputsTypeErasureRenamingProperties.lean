import Solcore.Frontend.LocalInputsTypeErasure
import Solcore.Frontend.LocalInputsRenaming
import Solcore.Frontend.LocalTypeInputsRenaming

/-! Relabeling already supplied inputs commutes with erasing their values.
This constructs no inhabitants for arbitrary type-only inputs. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

@[simp] theorem toTypeInputs_mapIds (inputs : LocalInputs)
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    (inputs.mapIds mapping injective).toTypeInputs =
      inputs.toTypeInputs.mapIds mapping injective := by
  cases inputs
  simp only [toTypeInputs, mapIds, LocalTypeInputs.mapIds, List.map_map,
    Function.comp_def, TypedLocalBinding.mapIds, LocalTypeBinding.mapIds]

end Solcore.Frontend.LocalInputs
