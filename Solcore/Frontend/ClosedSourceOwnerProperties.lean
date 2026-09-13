import Solcore.Frontend.RuntimeCapturedOwnerProperties
import Solcore.Frontend.RuntimeValueOwnerProperties
import Solcore.Frontend.ClosedSourceEvaluationCompatibility

/- Transport actual original successes, including every saved closure field.
Only owner injectivity is required: no lexical uniqueness, typing or world premise. -/
set_option autoImplicit false
namespace Solcore.Frontend

private theorem mapOwners_unit (mapping : Resolved.DeclarationId → Resolved.DeclarationId) :
    RuntimeValue.mapOwners mapping .unit = .unit := by simp only [RuntimeValue.mapOwners]

private theorem mapOwners_bool (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (value : Bool) :
    RuntimeValue.mapOwners mapping (.bool value) = .bool value := by simp only [RuntimeValue.mapOwners]

private theorem mapOwners_word (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (value : Core.Word) :
    RuntimeValue.mapOwners mapping (.word value) = .word value := by simp only [RuntimeValue.mapOwners]

private theorem mapOwners_pair (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (left right : RuntimeValue) :
    RuntimeValue.mapOwners mapping (.pair left right) = .pair (left.mapOwners mapping) (right.mapOwners mapping) := by
  simp only [RuntimeValue.mapOwners]

section
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
variable (injective : Function.Injective mapping)
include injective

/-- Every original expression success transports its complete value and store. -/
theorem ClosedSourceExpressionEvaluates.mapOwners
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceExpressionEvaluates owner names captured initialStore source value finalStore) :
    ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (initialStore.map (RuntimeValue.mapOwners mapping)) source
      (value.mapOwners mapping) (finalStore.map (RuntimeValue.mapOwners mapping)) := by
  induction original using ClosedSourceExpressionEvaluates.rec
    (motive_2 := fun owner names captured store source value final _ =>
      ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source
        (value.mapOwners mapping) (final.map (RuntimeValue.mapOwners mapping))) with
  | reference named found =>
    exact .reference ((LocalNameTable.lookup_mapIds_iff (ownerLocalIdMap mapping)
      (ownerLocalIdMap_injective mapping injective)).mpr named) (mapRuntimeCapturedOwners_lookup mapping injective found)
  | unit =>
    rw [mapOwners_unit]
    exact .unit
  | wordLiteral meaning =>
    rw [mapOwners_word]
    exact .wordLiteral meaning
  | group _ ih => exact .group ih
  | pair _ _ leftIH rightIH =>
    rw [mapOwners_pair]
    exact .pair leftIH rightIH
  | many _ _ headIH tailIH =>
    rw [mapOwners_pair]
    exact .many headIH tailIH
  | creation shape =>
    simp only [RuntimeValue.mapOwners_sourceClosure]
    exact .creation shape
  | call shape _ _ _ calleeIH argumentIH bodyIH =>
    simp only [RuntimeValue.mapOwners_sourceClosure] at calleeIH
    apply ClosedSourceExpressionEvaluates.call shape calleeIH argumentIH
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using bodyIH
  | conditionalTrue _ _ conditionIH branchIH =>
    simp only [mapOwners_bool] at conditionIH
    exact .conditionalTrue conditionIH branchIH
  | conditionalFalse _ _ conditionIH branchIH =>
    simp only [mapOwners_bool] at conditionIH
    exact .conditionalFalse conditionIH branchIH
  | logicalNot _ ih =>
    simp only [mapOwners_bool] at ih ⊢
    exact .logicalNot ih
  | bitNot _ ih =>
    simp only [mapOwners_word] at ih ⊢
    exact .bitNot ih
  | andTrue _ _ leftIH rightIH =>
    simp only [mapOwners_bool] at leftIH
    exact .andTrue leftIH rightIH
  | andFalse _ ih =>
    simp only [mapOwners_bool] at ih ⊢
    exact .andFalse ih
  | orTrue _ ih =>
    simp only [mapOwners_bool] at ih ⊢
    exact .orTrue ih
  | orFalse _ _ leftIH rightIH =>
    simp only [mapOwners_bool] at leftIH
    exact .orFalse leftIH rightIH
  | strictWordBinary _ _ meaning leftIH rightIH =>
    simp only [mapOwners_word] at leftIH rightIH
    rw [RuntimeValue.mapOwners_ofCore]
    exact .strictWordBinary leftIH rightIH meaning
  | bare =>
    rw [mapOwners_unit]
    exact .bare
  | expression _ ih => exact .expression ih
  | block _ ih => exact .block ih
  | binding _ _ initializerIH tailIH =>
    apply ClosedSourceBodyEvaluates.binding initializerIH
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using tailIH
  | inferred _ _ initializerIH tailIH =>
    apply ClosedSourceBodyEvaluates.inferred initializerIH
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using tailIH
  | discard _ _ expressionIH tailIH => exact .discard expressionIH tailIH
  | ifTrue _ _ conditionIH branchIH =>
    simp only [mapOwners_bool] at conditionIH
    exact .ifTrue conditionIH branchIH
  | ifFalse _ _ conditionIH branchIH =>
    simp only [mapOwners_bool] at conditionIH
    exact .ifFalse conditionIH branchIH
  | wordMatch _ choice _ scrutineeIH branchIH =>
    exact .wordMatch scrutineeIH ((runtimeWordMatchChooses_mapOwners_iff mapping).mpr choice) branchIH

/-- Every original body success transports fresh binding, selected branch and full endpoint. -/
theorem ClosedSourceBodyEvaluates.mapOwners
    {owner names captured initialStore source value finalStore}
    (original : ClosedSourceBodyEvaluates owner names captured initialStore source value finalStore) :
    ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (initialStore.map (RuntimeValue.mapOwners mapping)) source
      (value.mapOwners mapping) (finalStore.map (RuntimeValue.mapOwners mapping)) := by
  have independent := closedSourceBodyEvaluates_iff.mp original
  clear original
  induction independent with
  | bare =>
    rw [mapOwners_unit]
    exact .bare
  | expression child => exact .expression (child.mapOwners mapping injective)
  | block _ ih => exact .block ih
  | binding initializer _ tailIH =>
    apply ClosedSourceBodyEvaluates.binding (initializer.mapOwners mapping injective)
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using tailIH
  | inferred initializer _ tailIH =>
    apply ClosedSourceBodyEvaluates.inferred (initializer.mapOwners mapping injective)
    rw [freshLocalId_mapRuntimeNamesOwners mapping injective]
    simpa only [LocalNameTable.mapIds,
      mapRuntimeCapturedOwners,List.map_cons] using tailIH
  | discard child _ tailIH => exact .discard (child.mapOwners mapping injective) tailIH
  | ifTrue child _ branchIH =>
    have condition := child.mapOwners mapping injective
    simp only [mapOwners_bool] at condition
    exact .ifTrue condition branchIH
  | ifFalse child _ branchIH =>
    have condition := child.mapOwners mapping injective
    simp only [mapOwners_bool] at condition
    exact .ifFalse condition branchIH
  | wordMatch child choice _ branchIH =>
    exact .wordMatch (child.mapOwners mapping injective) ((runtimeWordMatchChooses_mapOwners_iff mapping).mpr choice) branchIH

end
end Solcore.Frontend
