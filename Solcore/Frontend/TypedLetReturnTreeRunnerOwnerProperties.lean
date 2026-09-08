import Solcore.Frontend.TypedLetReturnTreeOwnerProperties
import Solcore.Frontend.TypedLetReturnTreeRunner
import Solcore.Frontend.LocalInputsTypeErasureRenamingProperties

/-! Fixed-store owner relabeling preserves every optional result and actual
checkpoint. The original positional values are neither renamed nor reordered. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkTypedLetReturnTree?_mapOwner (inputs : LocalInputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) :
    (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).checkTypedLetReturnTree? types (mapping owner) body =
      inputs.checkTypedLetReturnTree? types owner body := by
  simp only [checkTypedLetReturnTree?, toTypeInputs_mapIds,
    elaborateTypedLetReturnTree?_mapOwner mapping injective]

theorem runTypedLetReturnTree?_mapOwner (inputs : LocalInputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnTree? types (mapping owner) fuel body store =
      inputs.runTypedLetReturnTree? types owner fuel body store := by
  simp only [runTypedLetReturnTree?, checkTypedLetReturnTree?_mapOwner inputs mapping injective,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end Solcore.Frontend.LocalInputs
