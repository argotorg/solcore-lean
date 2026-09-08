import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.LocalTypeInputsProperties
import Solcore.Frontend.LocalTypeInputsRenaming
import Solcore.Frontend.LocalOwnerRenaming

/-! Empty-start static declarations commute with injective owner relabeling.
The fresh-index induction uses annotation types only, without runtime values. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem map_bindFresh (inputs : LocalTypeInputs) (owner : Resolved.DeclarationId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    (sameFresh : Resolved.freshLocalId (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).ids =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner inputs.ids))
    (name : String) (type : Core.Ty) :
    (inputs.bindFresh owner name type).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) =
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).bindFresh (mapping owner) name type := by
  cases inputs
  simp only [LocalTypeInputs.mapIds, LocalTypeInputs.bindFresh, List.map_cons,
    LocalTypeBinding.mapIds, LocalTypeInputs.mk.injEq]
  congr 2
  exact sameFresh.symm

private theorem transport_from {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalTypeInputs} {parameters : List Syntax.FunctionParameter}
    (declared : RuntimeParametersDeclareFrom types owner initial parameters final)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    (sameIndex : (Resolved.freshLocalId (mapping owner)
        (initial.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).ids).binderIndex =
      (Resolved.freshLocalId owner initial.ids).binderIndex) :
    RuntimeParametersDeclareFrom types (mapping owner)
      (initial.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) parameters
      (final.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) := by
  induction declared with
  | nil => exact .nil
  | @cons initial final span name annotation type parameters meaning unused tail ih =>
      have sameFresh : Resolved.freshLocalId (mapping owner)
          (initial.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).ids =
          ownerLocalIdMap mapping (Resolved.freshLocalId owner initial.ids) := by
        change Resolved.LocalId.mk (mapping owner) _ = Resolved.LocalId.mk (mapping owner) _
        exact congrArg (Resolved.LocalId.mk (mapping owner)) sameIndex
      have nextInputs := map_bindFresh initial owner mapping injective sameFresh name.value type
      have nextIndex : (Resolved.freshLocalId (mapping owner)
          ((initial.bindFresh owner name.value type).mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).ids).binderIndex =
          (Resolved.freshLocalId owner (initial.bindFresh owner name.value type).ids).binderIndex := by
        rw [nextInputs]
        simp only [LocalTypeInputs.bindFresh_ids, Resolved.freshLocalId_cons_fresh_binderIndex, sameIndex]
      have mappedUnused : name.value ∉
          (initial.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).names.map Prod.fst := by
        simpa only [LocalTypeInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      exact .cons meaning mappedUnused (nextInputs ▸ ih nextIndex)

/-- Exact annotation-only inputs are relabeled without constructing values.
The public empty-start profile needs no extra fresh-index premise. -/
theorem RuntimeParametersDeclare.map_owner {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {inputs : LocalTypeInputs} (declared : RuntimeParametersDeclare types owner parameters inputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    RuntimeParametersDeclare types (mapping owner) parameters
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) :=
  transport_from declared mapping injective rfl

end Solcore.Frontend
