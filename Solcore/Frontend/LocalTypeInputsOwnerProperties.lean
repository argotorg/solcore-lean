import Solcore.Frontend.LocalOwnerRenaming
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Frontend.LocalTypeInputsRenaming

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
