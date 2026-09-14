import Solcore.Frontend.ClosedSourceEvaluatorOwnerProperties
import Solcore.Frontend.ClosedSourceOwnerProperties
import Solcore.Frontend.ClosedSourceEvaluatorCompletenessProperties
import Solcore.Frontend.ClosedSourceEvaluatorSoundnessProperties

/- Actual successful mapped endpoints have original preimages. No inverse owner
map, surjectivity or preselected endpoint-image premise is used to reflect them. -/
set_option autoImplicit false
namespace Solcore.Frontend
section
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
variable (injective : Function.Injective mapping)
include injective

/-- Every actual original expression endpoint in the mapped environment has an original preimage. -/
theorem ClosedSourceExpressionEvaluates.mapOwners_iff_exists
    {owner names captured store source value final} :
    ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source value final ↔
    ∃ before beforeStore, ClosedSourceExpressionEvaluates owner names captured store source before beforeStore ∧
      value = before.mapOwners mapping ∧ final = beforeStore.map (RuntimeValue.mapOwners mapping) := by
  constructor
  · intro original
    obtain ⟨budget,eventual⟩ := evaluateClosedSourceExpression?_eventually_complete original
    have actual := eventual budget (Nat.le_refl _)
    rw [evaluateClosedSourceExpression?_mapOwners mapping injective,Option.map_eq_some_iff] at actual
    obtain ⟨⟨before,beforeStore⟩,evaluated,same⟩ := actual
    exact ⟨before,beforeStore,evaluateClosedSourceExpression?_sound evaluated,
      (congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · rintro ⟨before,beforeStore,original,rfl,rfl⟩
    exact original.mapOwners mapping injective

/-- Actual mapped body successes reflect complete values and final stores without an endpoint assumption. -/
theorem ClosedSourceBodyEvaluates.mapOwners_iff_exists
    {owner names captured store source value final} :
    ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source value final ↔
    ∃ before beforeStore, ClosedSourceBodyEvaluates owner names captured store source before beforeStore ∧
      value = before.mapOwners mapping ∧ final = beforeStore.map (RuntimeValue.mapOwners mapping) := by
  constructor
  · intro original
    obtain ⟨budget,eventual⟩ := evaluateClosedSourceBody?_eventually_complete original
    have actual := eventual budget (Nat.le_refl _)
    rw [evaluateClosedSourceBody?_mapOwners mapping injective,Option.map_eq_some_iff] at actual
    obtain ⟨⟨before,beforeStore⟩,evaluated,same⟩ := actual
    exact ⟨before,beforeStore,evaluateClosedSourceBody?_sound evaluated,
      (congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · rintro ⟨before,beforeStore,original,rfl,rfl⟩
    exact original.mapOwners mapping injective

/-- Explicit mapped expression endpoints are equivalent to their original endpoints. -/
theorem ClosedSourceExpressionEvaluates.mapOwners_iff
    {owner names captured store source value final} :
    ClosedSourceExpressionEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source
      (value.mapOwners mapping) (final.map (RuntimeValue.mapOwners mapping)) ↔
    ClosedSourceExpressionEvaluates owner names captured store source value final := by
  rw [ClosedSourceExpressionEvaluates.mapOwners_iff_exists mapping injective]
  constructor
  · rintro ⟨before,beforeStore,original,values,stores⟩
    have valueSame := RuntimeValue.mapOwners_injective mapping injective values
    have storeSame := (List.map_inj_right (f := RuntimeValue.mapOwners mapping)
      (fun _ _ same => RuntimeValue.mapOwners_injective mapping injective same)).mp stores
    simpa only [valueSame,storeSame] using original
  · intro original
    exact ⟨value,final,original,rfl,rfl⟩

/-- Explicit mapped body endpoints are equivalent without requiring an onto owner map. -/
theorem ClosedSourceBodyEvaluates.mapOwners_iff
    {owner names captured store source value final} :
    ClosedSourceBodyEvaluates (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source
      (value.mapOwners mapping) (final.map (RuntimeValue.mapOwners mapping)) ↔
    ClosedSourceBodyEvaluates owner names captured store source value final := by
  rw [ClosedSourceBodyEvaluates.mapOwners_iff_exists mapping injective]
  constructor
  · rintro ⟨before,beforeStore,original,values,stores⟩
    have valueSame := RuntimeValue.mapOwners_injective mapping injective values
    have storeSame := (List.map_inj_right (f := RuntimeValue.mapOwners mapping)
      (fun _ _ same => RuntimeValue.mapOwners_injective mapping injective same)).mp stores
    simpa only [valueSame,storeSame] using original
  · intro original
    exact ⟨value,final,original,rfl,rfl⟩

end
end Solcore.Frontend
