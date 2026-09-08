import Solcore.Frontend.RuntimeParameters
import Solcore.Frontend.LocalInputsProperties
import Solcore.Frontend.LocalInputsRenaming
import Solcore.Frontend.LocalOwnerRenaming

/-! Empty-start runtime parameter binding commutes with injective owner
relabeling that leaves binder indices fixed. The proof follows the existing
fresh-allocation chain, not arbitrary local-ID allocator covariance. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem map_bindFresh (inputs : LocalInputs) (owner : Resolved.DeclarationId)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    (sameFresh : Resolved.freshLocalId (mapping owner)
        (inputs.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).ids =
      ownerLocalIdMap mapping (Resolved.freshLocalId owner inputs.ids))
    (name : String) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    (inputs.bindFresh owner name type value valueTyped).mapIds
        (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective) =
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)).bindFresh
          (mapping owner) name type value valueTyped := by
  cases inputs
  simp only [LocalInputs.mapIds, LocalInputs.bindFresh, List.map_cons,
    TypedLocalBinding.mapIds, LocalInputs.mk.injEq]
  congr 2
  exact sameFresh.symm

private theorem transport_from {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {initial final : LocalInputs} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument}
    (bound : RuntimeParametersBindFrom types owner initial parameters arguments final)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping)
    (sameIndex : (Resolved.freshLocalId (mapping owner)
        (initial.mapIds (ownerLocalIdMap mapping)
          (ownerLocalIdMap_injective mapping injective)).ids).binderIndex =
      (Resolved.freshLocalId owner initial.ids).binderIndex) :
    RuntimeParametersBindFrom types (mapping owner)
      (initial.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) parameters arguments
      (final.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) := by
  induction bound with
  | nil => exact .nil
  | @cons initial final span name annotation parameters argument arguments
      meaning unused tail ih =>
      have sameFresh : Resolved.freshLocalId (mapping owner)
          (initial.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).ids =
          ownerLocalIdMap mapping (Resolved.freshLocalId owner initial.ids) := by
        change Resolved.LocalId.mk (mapping owner) _ = Resolved.LocalId.mk (mapping owner) _
        exact congrArg (Resolved.LocalId.mk (mapping owner)) sameIndex
      have nextInputs := map_bindFresh initial owner mapping injective sameFresh
        name.value argument.type argument.value argument.valueTyped
      have nextIndex : (Resolved.freshLocalId (mapping owner)
          ((initial.bindFresh owner name.value argument.type argument.value
            argument.valueTyped).mapIds (ownerLocalIdMap mapping)
              (ownerLocalIdMap_injective mapping injective)).ids).binderIndex =
          (Resolved.freshLocalId owner
            (initial.bindFresh owner name.value argument.type argument.value
              argument.valueTyped).ids).binderIndex := by
        rw [nextInputs]
        simp only [LocalInputs.bindFresh_ids, Resolved.freshLocalId_cons_fresh_binderIndex,
          sameIndex]
      have mappedUnused : name.value ∉
          (initial.mapIds (ownerLocalIdMap mapping)
            (ownerLocalIdMap_injective mapping injective)).names.map Prod.fst := by
        simpa only [LocalInputs.mapIds_names, LocalNameTable.mapIds,
          List.map_map, Function.comp_def] using unused
      exact .cons meaning mappedUnused (nextInputs ▸ ih nextIndex)

/-- Relabeling an owner preserves the exact ordered typed input bundle produced
by independent empty-start binding. Runtime values and binder indices are unchanged. -/
theorem RuntimeParametersBind.map_owner {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {parameters : List Syntax.FunctionParameter}
    {arguments : List TypedRuntimeArgument} {inputs : LocalInputs}
    (bound : RuntimeParametersBind types owner parameters arguments inputs)
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
    (injective : Function.Injective mapping) :
    RuntimeParametersBind types (mapping owner) parameters arguments
      (inputs.mapIds (ownerLocalIdMap mapping)
        (ownerLocalIdMap_injective mapping injective)) :=
  transport_from bound mapping injective rfl

end Solcore.Frontend
