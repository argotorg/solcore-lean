import Solcore.Frontend.ClosedSourceOwnerReflectionProperties
import Solcore.Frontend.ClosedSourceDataExpressionProperties
import Solcore.Frontend.LocalExpressionRenamingSemantics

/- Owner relabeling keeps embedded Core values literal. The whole old resolution
and lowering boundary remains explicit when reflecting arbitrary raw endpoints. -/
set_option autoImplicit false
namespace Solcore.Frontend

/-- Relabeling an embedded ordered environment changes keys but no Core payload. -/
theorem mapRuntimeCapturedOwners_ofCore
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (environment : Resolved.Environment) :
    mapRuntimeCapturedOwners mapping (environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))) =
      (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map
        (fun row => (row.1,RuntimeValue.ofCore row.2)) := by
  simp only [mapRuntimeCapturedOwners,Resolved.LocalScope.mapIds,List.map_map,Function.comp_def,
    RuntimeValue.mapOwners_ofCore]

/-- Every element of an embedded Core store is fixed by owner relabeling. -/
theorem mapRuntimeStoreOwners_ofCore
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (store : Core.Store) :
    (store.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping) = store.map RuntimeValue.ofCore := by
  simp only [List.map_map,Function.comp_def,RuntimeValue.mapOwners_ofCore]

/-- Mapped resolution lowers to the literal old Core term and reflects every actual raw endpoint. -/
theorem ClosedSourceDataExpression.mapOwners_core_evaluates_iff
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    {owner : Resolved.DeclarationId} {names : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {source : Syntax.Expr} {actualValue : RuntimeValue}
    {actualFinal : List RuntimeValue} (fragment : ClosedSourceDataExpression source)
    {resolved : Resolved.Expr} {core : Core.Expr} (resolution : ResolvesLocalExpression names source resolved)
    (lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core) :
    ResolvesLocalExpression (LocalNameTable.mapIds (ownerLocalIdMap mapping) names) source
      (resolved.renameIds (ownerLocalIdMap mapping)) ∧
    Resolved.Lowers (Resolved.LocalScope.ids (Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment))
      (resolved.renameIds (ownerLocalIdMap mapping)) core ∧
    (ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      ((Resolved.LocalScope.mapIds (ownerLocalIdMap mapping) environment).map (fun row => (row.1,RuntimeValue.ofCore row.2)))
      (initialStore.map RuntimeValue.ofCore) source actualValue actualFinal ↔
    ∃ value finalStore, actualValue=RuntimeValue.ofCore value ∧ actualFinal=finalStore.map RuntimeValue.ofCore ∧
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore) := by
  refine ⟨resolution.mapIds _,?_,?_⟩
  · rw [Resolved.LocalScope.ids_mapIds]
    exact (Resolved.lowers_renameIds_iff (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).mpr lowered
  · constructor
    · intro actual
      have mapped : ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
          (mapRuntimeCapturedOwners mapping (environment.map (fun row => (row.1,RuntimeValue.ofCore row.2))))
          ((initialStore.map RuntimeValue.ofCore).map (RuntimeValue.mapOwners mapping)) source actualValue actualFinal := by
        simpa only [mapRuntimeCapturedOwners_ofCore,mapRuntimeStoreOwners_ofCore] using actual
      obtain ⟨before,beforeStore,original,values,stores⟩ :=
        (ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective).mp mapped
      obtain ⟨value,finalStore,beforeEq,beforeStoreEq,evaluated⟩ :=
        (fragment.core_evaluates_iff resolution lowered).mp original
      refine ⟨value,finalStore,?_,?_,evaluated⟩
      · simpa only [beforeEq,RuntimeValue.mapOwners_ofCore] using values
      · simpa only [beforeStoreEq,mapRuntimeStoreOwners_ofCore] using stores
    · rintro ⟨value,finalStore,rfl,rfl,evaluated⟩
      have original := (fragment.core_evaluates_iff (owner:=owner) resolution lowered).mpr
        ⟨value,finalStore,rfl,rfl,evaluated⟩
      simpa only [mapRuntimeCapturedOwners_ofCore,mapRuntimeStoreOwners_ofCore,RuntimeValue.mapOwners_ofCore] using
        original.mapOwners mapping injective

end Solcore.Frontend
