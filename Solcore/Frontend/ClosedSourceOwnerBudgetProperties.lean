import Solcore.Frontend.ClosedSourceEvaluatorOwnerProperties
import Solcore.Frontend.ClosedSourceEvaluatorThresholdProperties

/- Full finite observations reflect actual endpoints, not assumed endpoint images.
Successful originals retain one positive cutoff for both complete runners. -/
set_option autoImplicit false
namespace Solcore.Frontend
section
variable (mapping : Resolved.DeclarationId → Resolved.DeclarationId)
variable (injective : Function.Injective mapping)
include injective

/-- Every actual mapped expression success has a complete preimage at the same budget. -/
theorem evaluateClosedSourceExpression?_mapOwners_some_iff_exists
    {budget owner names captured store source value final} :
    evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source = some (value,final) ↔
    ∃ before beforeStore, evaluateClosedSourceExpression? budget owner names captured store source = some (before,beforeStore) ∧
      value = before.mapOwners mapping ∧ final = beforeStore.map (RuntimeValue.mapOwners mapping) := by
  rw [evaluateClosedSourceExpression?_mapOwners mapping injective,Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨before,beforeStore⟩,ran,same⟩
    exact ⟨before,beforeStore,ran,(congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · rintro ⟨before,beforeStore,ran,rfl,rfl⟩
    exact ⟨(before,beforeStore),ran,rfl⟩

/-- Every actual mapped body success has a complete preimage at the same budget. -/
theorem evaluateClosedSourceBody?_mapOwners_some_iff_exists
    {budget owner names captured store source value final} :
    evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source = some (value,final) ↔
    ∃ before beforeStore, evaluateClosedSourceBody? budget owner names captured store source = some (before,beforeStore) ∧
      value = before.mapOwners mapping ∧ final = beforeStore.map (RuntimeValue.mapOwners mapping) := by
  rw [evaluateClosedSourceBody?_mapOwners mapping injective,Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨before,beforeStore⟩,ran,same⟩
    exact ⟨before,beforeStore,ran,(congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩
  · rintro ⟨before,beforeStore,ran,rfl,rfl⟩
    exact ⟨(before,beforeStore),ran,rfl⟩

/-- Finite expression absence is equivalent at the same budget, without classifying its cause. -/
theorem evaluateClosedSourceExpression?_mapOwners_none_iff
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Expr) :
    evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source = none ↔
    evaluateClosedSourceExpression? budget owner names captured store source = none := by
  rw [evaluateClosedSourceExpression?_mapOwners mapping injective,Option.map_eq_none_iff]

/-- Finite body absence is equivalent at the same budget, with no success or cutoff premise. -/
theorem evaluateClosedSourceBody?_mapOwners_none_iff
    (budget : Nat) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue) (source : Syntax.Block) :
    evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
      (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source = none ↔
    evaluateClosedSourceBody? budget owner names captured store source = none := by
  rw [evaluateClosedSourceBody?_mapOwners mapping injective,Option.map_eq_none_iff]

/-- A successful original expression has one positive exact cutoff shared by both complete runners. -/
theorem ClosedSourceExpressionEvaluates.mapOwners_exact_depth_threshold
    {owner names captured store source value final}
    (original : ClosedSourceExpressionEvaluates owner names captured store source value final) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      (evaluateClosedSourceExpression? budget owner names captured store source =
        if required ≤ budget then some (value,final) else none) ∧
      (evaluateClosedSourceExpression? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
        if required ≤ budget then some (value.mapOwners mapping,final.map (RuntimeValue.mapOwners mapping)) else none) := by
  obtain ⟨required,positive,cutoff⟩ := original.exact_depth_threshold
  refine ⟨required,positive,fun budget => ⟨cutoff budget,?_⟩⟩
  rw [evaluateClosedSourceExpression?_mapOwners mapping injective,cutoff budget]
  split <;> rfl

/-- A successful original body has the same exact positive cutoff after owner relabeling. -/
theorem ClosedSourceBodyEvaluates.mapOwners_exact_depth_threshold
    {owner names captured store source value final}
    (original : ClosedSourceBodyEvaluates owner names captured store source value final) :
    ∃ required : Nat, 0 < required ∧ ∀ budget,
      (evaluateClosedSourceBody? budget owner names captured store source =
        if required ≤ budget then some (value,final) else none) ∧
      (evaluateClosedSourceBody? budget (mapping owner) (LocalNameTable.mapIds (ownerLocalIdMap mapping) names)
        (mapRuntimeCapturedOwners mapping captured) (store.map (RuntimeValue.mapOwners mapping)) source =
        if required ≤ budget then some (value.mapOwners mapping,final.map (RuntimeValue.mapOwners mapping)) else none) := by
  obtain ⟨required,positive,cutoff⟩ := original.exact_depth_threshold
  refine ⟨required,positive,fun budget => ⟨cutoff budget,?_⟩⟩
  rw [evaluateClosedSourceBody?_mapOwners mapping injective,cutoff budget]
  split <;> rfl

end
end Solcore.Frontend
