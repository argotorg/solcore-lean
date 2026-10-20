import Solcore.SourceSemantics.SourceInferenceNormalizedMatchContinuation

/-! Index expressions and places retain normalized formation through their
actual base inference, fresh mapping variables, unification and key inference. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness SourceInferenceRequirementFormation

private theorem unify_fields {state result : State} {left right : Ty}
    (accepted : Detail.unify state left right = .ok result) :
    result.localBinders = state.localBinders ∧ result.requirements = state.requirements := by
  unfold Detail.unify at accepted
  cases unified : state.inference.unify left right with
  | error error => simp [unified, Detail.liftUnification, bind, Except.bind] at accepted
  | ok inference =>
    simp only [unified, Detail.liftUnification, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
    cases accepted
    exact ⟨rfl,rfl⟩

private theorem recording_fields
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {type : Ty} {form : ExpressionForm} {expected : Option Ty} {state : State}
    {result : InferredExpression × State}
    (accepted : recordExpressionWithExpected context source id type form [] expected state = .ok result) :
    result.2.localBinders = state.localBinders ∧ state.nodes <+: result.2.nodes := by
  obtain ⟨fitted, run, _, resultEq⟩ := recordExpressionWithExpected_success_record accepted
  rw [resultEq]
  refine ⟨?_, ?_⟩
  · exact congrArg LexicalScope.binders (localReadScope_withExpected_lexicalScope run)
  · rw [State.recordNode_nodes, (withExpected_occurrenceState_eq run).1]
    exact List.prefix_append _ _

private structure MappingPrefix (base final : State) : Prop where
  progress : base.InferenceProgress final
  ready : final.InferenceReady
  keyBelow : (final.resolve base.fresh.1).VariablesBelow final.inference.next
  valueBelow : base.fresh.2.fresh.1.VariablesBelow final.inference.next
  nodes : final.nodes = base.nodes
  occurrence : final.nextOccurrence = base.nextOccurrence
  binders : final.localBinders = base.localBinders
  requirements : final.requirements = base.requirements

private theorem mapping_prefix {base final : State} {type : Ty}
    (ready : base.InferenceReady) (below : type.VariablesBelow base.inference.next)
    (accepted : unify base.fresh.2.fresh.2 type
      (.mapping base.fresh.1 base.fresh.2.fresh.1) = .ok final) :
    MappingPrefix base final := by
  have key := fresh_eq_inferenceProperties ready (type := base.fresh.1)
    (next := base.fresh.2) rfl
  have value := fresh_eq_inferenceProperties key.2.1 (type := base.fresh.2.fresh.1)
    (next := base.fresh.2.fresh.2) rfl
  have baseBelow := below.weaken (key.1.trans value.1).next_le
  have keyBelow := key.2.2.weaken value.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow,value.2.2⟩
  have unified := unify_inferenceProgress value.2.1.solved baseBelow mappingBelow accepted
  have finalReady := unify_preserves_inferenceReady value.2.1 baseBelow mappingBelow accepted
  have fields := unify_fields accepted
  have occurrences := unify_occurrenceState_eq accepted
  exact ⟨key.1.trans (value.1.trans unified),finalReady,
    finalReady.solved.variablesBelow_apply (keyBelow.weaken unified.next_le),
    value.2.2.weaken unified.next_le,occurrences.1,occurrences.2,fields.1,fields.2⟩

private theorem fresh_formed {semantic : SourceSemantics.Context}
    {context : SourceInference.Context} {outer : Substitution}
    (formation : InferenceFormationContext semantic context outer) (state : State) :
    TypeAdmissible semantic (outer.apply state.fresh.1) :=
  type_applySubstitution_residual formation.residual formation.range
    (.variableOfResidual formation.scope.binders formation.residual ⟨state.inference.next⟩)

theorem inferPlaceFuel_index_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {target base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {initial : State}
    (form : target.value = .index base brackets key)
    (baseIH : InferPlaceFuelFormation semantic outer fuel context base initial)
    (keyIH : ∀ keyType state, InferExprFuelFormation semantic outer fuel context key
      (some (state.resolve keyType)) state) :
    InferPlaceFuelFormation semantic outer (fuel + 1) context target initial := by
  intro ready nodes formed formation result accepted continuation noCapture
  unfold inferPlaceFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases baseRun : inferPlaceFuel fuel context base initial with
  | error error => simp [baseRun] at accepted
  | ok basePair =>
    rcases basePair with ⟨basePlace,baseState⟩
    simp only [baseRun] at accepted
    cases unified : unify baseState.fresh.2.fresh.2 basePlace.type
        (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) with
    | error error => simp [unified] at accepted
    | ok unifiedState =>
      simp only [unified] at accepted
      cases keyRun : inferExprFuel fuel context key (some (unifiedState.resolve baseState.fresh.1))
          unifiedState with
      | error error => simp [keyRun] at accepted
      | ok keyPair =>
        rcases keyPair with ⟨keyValue,keyState⟩
        simp only [keyRun, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
        subst result
        have baseProperties := inferPlaceFuel_inferenceProperties ready
          formation.validated formation.functionShapes baseRun
        have mappingPrefix := mapping_prefix baseProperties.2.1 baseProperties.2.2 unified
        have baseNodes := (inferPlaceFuel_occurrenceBoundExtends baseRun).nodesBelowNextOccurrence nodes
        have unifiedNodes : unifiedState.NodesBelowNextOccurrence := by
          simpa only [State.NodesBelowNextOccurrence, mappingPrefix.nodes, mappingPrefix.occurrence] using baseNodes
        have expectedBelow : ∀ type ∈ some (unifiedState.resolve baseState.fresh.1),
            type.VariablesBelow unifiedState.inference.next := by
          intro type member
          cases Option.mem_def.mp member
          exact mappingPrefix.keyBelow
        have keyProperties := inferExprFuel_inferenceProperties mappingPrefix.ready
          formation.validated formation.functionShapes expectedBelow keyRun
        have unifiedContinuation := continuation.trans keyProperties.1.substitution_extends
        have basePrefix : baseState.nodes <+: keyState.nodes := by
          rw [← mappingPrefix.nodes]
          exact inferExprFuel_preserves_nodesPrefix keyRun List.prefix_rfl unifiedNodes (Nat.le_refl _)
        have baseFormed := baseIH ready nodes formed formation _ baseRun
          (unifiedContinuation.trans mappingPrefix.progress.substitution_extends)
          (noCapture.of_prefix basePrefix)
        have keyFormed := keyIH baseState.fresh.1 unifiedState mappingPrefix.ready unifiedNodes
          (baseFormed.2.congr mappingPrefix.binders mappingPrefix.requirements) formation expectedBelow
          (by
            intro type member
            cases Option.mem_def.mp member
            exact (unifiedContinuation _).symm ▸ fresh_formed formation baseState)
          _ keyRun continuation noCapture
        exact ⟨(continuation _).symm ▸ fresh_formed formation baseState.fresh.2,keyFormed.2⟩

theorem inferExprFuel_index_formation
    {semantic : SourceSemantics.Context} {outer : Substitution}
    {fuel : Nat} {context : SourceInference.Context} {expression base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan} {expected : Option Ty} {initial : State}
    (form : expression.value = .index base brackets key)
    (baseIH : InferExprFuelFormation semantic outer fuel context base none initial.allocateExpressionId.2)
    (keyIH : ∀ keyType state, InferExprFuelFormation semantic outer fuel context key
      (some (state.resolve keyType)) state) :
    InferExprFuelFormation semantic outer (fuel + 1) context expression expected initial := by
  intro ready nodes formed formation expectedBelow expectedFormed result accepted continuation noCapture
  unfold inferExprFuel at accepted
  simp only [form, bind, Except.bind] at accepted
  cases baseRun : inferExprFuel fuel context base none initial.allocateExpressionId.2 with
  | error error => simp [baseRun] at accepted
  | ok basePair =>
    rcases basePair with ⟨baseValue,baseState⟩
    simp only [baseRun] at accepted
    cases unified : unify baseState.fresh.2.fresh.2 baseValue.type
        (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1) with
    | error error => simp [unified] at accepted
    | ok unifiedState =>
      simp only [unified] at accepted
      cases keyRun : inferExprFuel fuel context key (some (unifiedState.resolve baseState.fresh.1))
          unifiedState with
      | error error => simp [keyRun] at accepted
      | ok keyPair =>
        rcases keyPair with ⟨keyValue,keyState⟩
        simp only [keyRun] at accepted
        have allocation : initial.InferenceProgress initial.allocateExpressionId.2 ∧
            initial.allocateExpressionId.2.InferenceReady :=
          ⟨State.InferenceProgress.allocateExpressionId initial ready.solved, ready.allocateExpressionId⟩
        have allocatedNodes := (State.OccurrenceBoundExtends.allocateExpressionId initial).nodesBelowNextOccurrence nodes
        have baseProperties := inferExprFuel_inferenceProperties allocation.2
          formation.validated formation.functionShapes (by simp) baseRun
        have mappingPrefix := mapping_prefix baseProperties.2.1 baseProperties.2.2 unified
        have baseNodes := (inferExprFuel_occurrenceBoundExtends baseRun).nodesBelowNextOccurrence allocatedNodes
        have unifiedNodes : unifiedState.NodesBelowNextOccurrence := by
          simpa only [State.NodesBelowNextOccurrence, mappingPrefix.nodes, mappingPrefix.occurrence] using baseNodes
        have keyExpectedBelow : ∀ type ∈ some (unifiedState.resolve baseState.fresh.1),
            type.VariablesBelow unifiedState.inference.next := by
          intro type member
          cases Option.mem_def.mp member
          exact mappingPrefix.keyBelow
        have keyProperties := inferExprFuel_inferenceProperties mappingPrefix.ready
          formation.validated formation.functionShapes keyExpectedBelow keyRun
        have throughKey := allocation.1.trans
          (baseProperties.1.trans (mappingPrefix.progress.trans keyProperties.1))
        have valueBelow := keyProperties.1.resolve_variablesBelow mappingPrefix.valueBelow
        have expectedAtKey : ∀ type ∈ expected, type.VariablesBelow keyState.inference.next :=
          fun type member => (expectedBelow type member).weaken throughKey.next_le
        have recorded := recordExpressionWithExpected_inferenceProperties keyProperties.2.1
          valueBelow expectedAtKey accepted
        have recordFields := recording_fields accepted
        have keyContinuation := continuation.trans recorded.1.substitution_extends
        have unifiedContinuation := keyContinuation.trans keyProperties.1.substitution_extends
        have keyNoCapture := noCapture.of_prefix recordFields.2
        have basePrefix : baseState.nodes <+: keyState.nodes := by
          rw [← mappingPrefix.nodes]
          exact inferExprFuel_preserves_nodesPrefix keyRun List.prefix_rfl unifiedNodes (Nat.le_refl _)
        have baseFormed := baseIH allocation.2 allocatedNodes (formed.congr rfl rfl) formation
          (by simp) (by simp) _ baseRun (unifiedContinuation.trans mappingPrefix.progress.substitution_extends)
          (keyNoCapture.of_prefix basePrefix)
        have keyFormed := keyIH baseState.fresh.1 unifiedState mappingPrefix.ready unifiedNodes
          (baseFormed.2.congr mappingPrefix.binders mappingPrefix.requirements) formation keyExpectedBelow
          (by
            intro type member
            cases Option.mem_def.mp member
            exact (unifiedContinuation _).symm ▸ fresh_formed formation baseState)
          _ keyRun keyContinuation keyNoCapture
        have fitted := recordExpressionWithExpected_normalized_formation formation.toFormationContext continuation
          ((keyContinuation _).symm ▸ fresh_formed formation baseState.fresh.2) expectedFormed accepted
        exact ⟨fitted.1,keyFormed.2.of_new_rows recordFields.1 fitted.2⟩

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
