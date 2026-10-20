import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps

/-! Assignable mapping places retain events from their base and key through
the actual fresh variables and mapping unification. -/
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
    {initial : State}
    {baseResult : PlaceResolution} {keyResult : InferredExpression}
    {baseState keyState valueState mappingState indexState : State}
    {keyType valueType : Ty} {final : PlaceResolution × State}

theorem place_group
    {inner : Syntax.Expr} {child : PlaceResolution × State}
    (form : source.value = .group inner)
    (childAccepted : inferPlaceFuel fuel context inner initial = .ok child)
    (accepted : inferPlaceFuel (fuel + 1) context source initial = .ok final)
    (lifetime : GeneralizationLifetime event initial.inference.next child.2 [child.1.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have same : child = final := by simpa only [inferPlaceFuel, form, Except.ok.injEq, childAccepted] using accepted
  cases same
  exact lifetime

theorem place_index_base
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (form : source.value = .index base brackets key)
    (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseResult, baseState))
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingAccepted : Detail.unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyAccepted : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (accepted : inferPlaceFuel (fuel + 1) context source initial = .ok final)
    (lifetime : GeneralizationLifetime event initial.inference.next baseState [baseResult.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have baseProperties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical baseAccepted
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
  have baseWellFormed := (inferPlaceFuel_direct_progress baseAccepted).wellFormed wellFormed
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
  have resultEq : ({baseResult with
      projections := baseResult.projections ++ [.index keyResult.id]
      type := indexState.resolve valueType}, indexState) = final := by
    simpa only [inferPlaceFuel, form, baseAccepted, keyFresh, valueFresh,
      mappingAccepted, keyAccepted, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] using accepted
  cases resultEq
  exact indexLife.replaceOutputs (by
    intro type member
    cases List.mem_singleton.mp member
    exact safe_resolved indexProperties.2.1 (indexLife.values _ (by simp)))

theorem place_index_key
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (form : source.value = .index base brackets key)
    (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseResult, baseState))
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingAccepted : Detail.unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyAccepted : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (accepted : inferPlaceFuel (fuel + 1) context source initial = .ok final)
    (lifetime : GeneralizationLifetime event mappingState.inference.next indexState [keyResult.type]) :
    GeneralizationLifetime event initial.inference.next final.2 [final.1.type] := by
  have baseProperties := inferPlaceFuel_inferenceProperties ready catalog.formation catalog.canonical baseAccepted
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
  have indexLife := lifetime.weaken_entry prefixProgress.next_le
  have resultEq : ({baseResult with
      projections := baseResult.projections ++ [.index keyResult.id]
      type := indexState.resolve valueType}, indexState) = final := by
    simpa only [inferPlaceFuel, form, baseAccepted, keyFresh, valueFresh,
      mappingAccepted, keyAccepted, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq] using accepted
  cases resultEq
  exact indexLife.replaceOutputs (by
    intro type member
    cases List.mem_singleton.mp member
    exact safe_resolved indexProperties.2.1 valueSafe)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
