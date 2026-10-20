import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps

/-! Mapping index inference retains events created by either the base or the
key through its actual fresh variables, mapping unification and recording. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail

namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context}
    {source base key : Syntax.Expr} {brackets : Syntax.SourceSpan}
    {expected : Option Ty} {initial allocated : State} {id : ExpressionId}
    {baseResult keyResult : InferredExpression}
    {baseState keyState valueState mappingState indexState : State}
    {keyType valueType : Ty} {final : InferredExpression × State}

theorem index_base
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .index base brackets key)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (baseAccepted : inferExprFuel fuel context base none allocated = .ok (baseResult, baseState))
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingAccepted : Detail.unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyAccepted : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event allocated.inference.next baseState [baseResult.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have lifetime : GeneralizationLifetime event initial.inference.next baseState [baseResult.type] := by
    simpa only [sameNext] using lifetime
  have baseProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical (by simp) baseAccepted
  have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have keyLife : GeneralizationLifetime event initial.inference.next keyState [baseResult.type, keyType] := by
    simpa only [keyFresh, List.singleton_append] using lifetime.fresh baseProperties.2.1
  have valueLife : GeneralizationLifetime event initial.inference.next valueState
      [baseResult.type, keyType, valueType] := by
    simpa only [valueFresh, List.cons_append, List.nil_append] using keyLife.fresh keyProperties.2.1
  have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow mappingAccepted
  have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow mappingAccepted
  have mappingLife := valueLife.unify valueProperties.2.1 baseBelow mappingBelow
    (valueLife.values _ (by simp))
    ((safe_mapping_iff _ _ _ _).2 ⟨valueLife.values _ (by simp), valueLife.values _ (by simp)⟩)
    mappingAccepted
  have allocatedWellFormed : allocated.RequirementsWellFormed := by
    rw [allocatedEq]
    exact wellFormed
  have baseWellFormed := (inferExprFuel_direct_progress baseAccepted).wellFormed allocatedWellFormed
  have valueWellFormed : valueState.RequirementsWellFormed := by
    rw [← show keyState.fresh.2 = valueState from congrArg Prod.snd valueFresh,
      ← show baseState.fresh.2 = keyState from congrArg Prod.snd keyFresh]
    exact baseWellFormed
  have mappingWellFormed := unify_preserves_requirementsWellFormed mappingAccepted valueWellFormed
  have resolvedKeyBelow := mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)
  have keyExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact resolvedKeyBelow
  have keySafe : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      Safe binder.scheme.quantified mappingState type := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact safe_resolved mappingReady (mappingLife.values _ (by simp))
  have indexProperties := inferExprFuel_inferenceProperties mappingReady
    catalog.formation catalog.canonical keyExpected keyAccepted
  have indexLife := mappingLife.inferExpr mappingReady mappingWellFormed catalog
    keyExpected keySafe keyAccepted
  have valueBelow := valueProperties.2.2.weaken
    (Nat.le_trans mappingProgress.next_le indexProperties.1.next_le)
  have prefixProgress := baseProperties.1.trans (keyProperties.1.trans
    (valueProperties.1.trans (mappingProgress.trans indexProperties.1)))
  have recorded : recordExpressionWithExpected context source id (indexState.resolve valueType)
      (.index baseResult.id keyResult.id) [] expected indexState = .ok final := by
    simpa only [inferExprFuel, allocation, form, baseAccepted, keyFresh, valueFresh,
      mappingAccepted, keyAccepted, bind, Except.bind] using accepted
  have finalLife := indexLife.recordExpression catalog.catalog indexProperties.2.1
    (indexProperties.2.1.solved.variablesBelow_apply valueBelow)
    (fun type member => (sameNext ▸ expectedBelow type member).weaken prefixProgress.next_le)
    (safe_resolved indexProperties.2.1 (indexLife.values _ (by simp)))
    (fun type member => indexLife.older type (expectedBelow type member)) recorded
  exact finalLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

theorem index_key
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (form : source.value = .index base brackets key)
    (allocation : initial.allocateExpressionId = (id, allocated))
    (baseAccepted : inferExprFuel fuel context base none allocated = .ok (baseResult, baseState))
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingAccepted : Detail.unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyAccepted : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (accepted : inferExprFuel (fuel + 1) context source expected initial = .ok final)
    (lifetime : GeneralizationLifetime event mappingState.inference.next indexState [keyResult.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have allocatedEq : allocated = initial.allocateExpressionId.2 :=
    (congrArg Prod.snd allocation).symm
  have sameNext : allocated.inference.next = initial.inference.next := by
    rw [allocatedEq]; rfl
  have baseProperties := inferExprFuel_inferenceProperties
    (allocatedEq ▸ ready.allocateExpressionId) catalog.formation catalog.canonical (by simp) baseAccepted
  have keyProperties := fresh_eq_inferenceProperties baseProperties.2.1 keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have baseBelow := baseProperties.2.2.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow mappingAccepted
  have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow mappingAccepted
  have resolvedKeyBelow := mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)
  have keyExpected : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact resolvedKeyBelow
  have indexProperties := inferExprFuel_inferenceProperties mappingReady
    catalog.formation catalog.canonical keyExpected keyAccepted
  have prefixProgress := baseProperties.1.trans
    (keyProperties.1.trans (valueProperties.1.trans mappingProgress))
  have valueAtMapping := valueProperties.2.2.weaken mappingProgress.next_le
  have valueSafe := lifetime.older valueType valueAtMapping
  have indexLife := lifetime.weaken_entry (sameNext ▸ prefixProgress.next_le)
  have recorded : recordExpressionWithExpected context source id (indexState.resolve valueType)
      (.index baseResult.id keyResult.id) [] expected indexState = .ok final := by
    simpa only [inferExprFuel, allocation, form, baseAccepted, keyFresh, valueFresh,
      mappingAccepted, keyAccepted, bind, Except.bind] using accepted
  have finalLife := indexLife.recordExpression catalog.catalog indexProperties.2.1
    (indexProperties.2.1.solved.variablesBelow_apply (valueAtMapping.weaken indexProperties.1.next_le))
    (fun type member => (sameNext ▸ expectedBelow type member).weaken
      (Nat.le_trans prefixProgress.next_le indexProperties.1.next_le))
    (safe_resolved indexProperties.2.1 valueSafe)
    (fun type member => indexLife.older type (expectedBelow type member)) recorded
  exact finalLife.restrict_outputs (by intro type member; exact List.mem_append_right _ member)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
