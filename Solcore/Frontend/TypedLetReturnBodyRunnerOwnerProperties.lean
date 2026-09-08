import Solcore.Frontend.TypedLetReturnBodyOwnerProperties
import Solcore.Frontend.TypedLetReturnBodyRunner
import Solcore.Frontend.LocalInputsTypeErasureRenamingProperties

/-! At a fixed store, owner-only relabeling preserves complete optional body
results, including genuine checkpoints. Actual values retain their positions. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalInputs

theorem checkTypedLetReturnBody?_mapOwner (inputs : LocalInputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (body : Syntax.Block) :
    (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).checkTypedLetReturnBody? types (mapping owner) body =
      inputs.checkTypedLetReturnBody? types owner body := by
  simp only [checkTypedLetReturnBody?, toTypeInputs_mapIds,
    elaborateTypedLetReturnBody?_mapOwner mapping injective]

theorem runTypedLetReturnBody?_mapOwner (inputs : LocalInputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) (types : TypeNameTable)
    (owner : Resolved.DeclarationId) (fuel : Nat) (body : Syntax.Block) (store : Core.Store) :
    (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnBody? types (mapping owner) fuel body store =
      inputs.runTypedLetReturnBody? types owner fuel body store := by
  simp only [runTypedLetReturnBody?, checkTypedLetReturnBody?_mapOwner inputs mapping injective,
    mapIds_environment, Resolved.LocalScope.values_mapIds]

end Solcore.Frontend.LocalInputs
