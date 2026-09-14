import Solcore.Frontend.ClosedSourceOwnerCoreExpressionProperties
import Solcore.Frontend.ClosedSourceDataBodyProperties
import Solcore.Frontend.ComputationReturnTreeOwnerProperties

/- Preserve the old complete shared-checker and exact runtime-ID premises.
An actual mapped result becomes a Core image only through the old gated bridge. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Mapped body checking retains the same Core/type pair and complete actual-output image. -/
theorem ClosedSourceDataBody.mapOwners_core_evaluates_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {initialStore : Core.Store} {body : Syntax.Block}
    {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} (fragment : ClosedSourceDataBody body)
    {core : Core.Expr} {type : Core.Ty}
    (accepted : elaborateComputationReturnTree? elaborateLocalExpression? types owner inputs body = some (core,type))
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context) :
    elaborateComputationReturnTree? elaborateLocalExpression? types (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)) body = some (core,type) ∧
    Resolved.LocalScope.ids (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment) =
      Resolved.LocalScope.ids (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).context ∧
    (ClosedSourceBodyEvaluates (mapping owner)
      (inputs.mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).names
      ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) body actualValue actualFinal ↔
    ∃ value finalStore, actualValue=RuntimeValue.ofCore value ∧ actualFinal=finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore) := by
  refine ⟨?_,?_,?_⟩
  · rw [elaborateComputationReturnTree?_mapOwner mapping injective elaborateLocalExpression?
      (elaborateLocalExpression?_mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective))]
    exact accepted
  · simpa only [LocalTypeInputs.mapIds_context,Resolved.LocalScope.ids_mapIds] using
      congrArg (List.map (ownerLocalIdMap mapping)) sameIds
  · constructor
    · intro actual
      have mapped : ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) inputs.names)
          (mapRuntimeCapturedOwners mapping (environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))))
          ((initialStore.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping)) body actualValue actualFinal := by
        simpa only [LocalTypeInputs.mapIds_names,mapRuntimeCapturedOwners_ofCore,mapRuntimeStoreOwners_ofCore] using actual
      obtain ⟨before,beforeStore,original,values,stores⟩ :=
        (ClosedSourceBodyEvaluates.mapOwners_iff_exists mapping injective).mp mapped
      obtain ⟨value,finalStore,beforeEq,beforeStoreEq,evaluated⟩ :=
        (fragment.core_evaluates_iff accepted sameIds).mp original
      refine ⟨value,finalStore,?_,?_,evaluated⟩
      · simpa only [beforeEq,RuntimeValue.mapOwners_ofCore] using values
      · simpa only [beforeStoreEq,mapRuntimeStoreOwners_ofCore] using stores
    · rintro ⟨value,finalStore,rfl,rfl,evaluated⟩
      have original := (fragment.core_evaluates_iff accepted sameIds).mpr
        ⟨value,finalStore,rfl,rfl,evaluated⟩
      simpa only [LocalTypeInputs.mapIds_names,mapRuntimeCapturedOwners_ofCore,
        mapRuntimeStoreOwners_ofCore,RuntimeValue.mapOwners_ofCore] using original.mapOwners mapping injective

end Solcore.Frontend
