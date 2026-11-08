import Solcore.SourceSemantics.Internal.Execution.CallInputs
import Solcore.SourceSemantics.Internal.Privacy.LifetimeContinuations
import Solcore.SourceSemantics.Internal.Privacy.Lifetimes
import Solcore.SourceSemantics.Internal.Compiled.OperationalState
import Solcore.SourceSemantics.Internal.Execution.StatementProgress

/-!
# Progress of expressions

Each expression child continues to the final state of its root call. These modules sit above the
compiled body layer.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualExpressionLifetime
/-! Events in actual expression children survive their parent's remaining
inference steps. Every prefix and continuation comes from the recorded call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness.ProtectedVariables

private theorem lambdaPrefix_unique
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial : State}
    {leftType rightType : Ty} {leftState rightState : State}
    (left : LambdaPrefixFacts context expected annotation types initial leftType leftState)
    (right : LambdaPrefixFacts context expected annotation types initial rightType rightState) :
    leftType = rightType ∧ leftState = rightState := by
  cases left <;> cases right <;> simp_all

theorem ChildStep.lifetime_expression
    {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial final : State} {value : InferredExpression}
    {child : CallIndex}
    (inputs : (CallIndex.expression fuel context source expected initial value final).Inputs)
    (step : ChildStep (.expression fuel context source expected initial value final) child)
    (life : GeneralizationLifetime event child.initial.inference.next child.final child.outputTypes) :
    GeneralizationLifetime event initial.inference.next final [value.type] := by
  cases step with
  | expression_group accepted form allocation childAccepted =>
      exact GeneralizationLifetime.group inputs.ready inputs.catalog inputs.bounds
        form allocation childAccepted accepted life
  | expression_tuple accepted form allocation childAccepted =>
      exact GeneralizationLifetime.tuple inputs.ready inputs.catalog inputs.bounds
        form allocation childAccepted accepted life
  | expression_unary accepted form allocation childAccepted =>
      exact GeneralizationLifetime.unary inputs.ready inputs.catalog inputs.bounds
        form allocation childAccepted accepted life
  | expression_binary_left accepted form allocation childAccepted =>
      obtain ⟨leftResult, leftState, rightResult, rightState, leftRun, rightRun, _⟩ :=
        inferExprFuel_success_binary_facts form allocation accepted
      cases Except.ok.inj (leftRun.symm.trans childAccepted)
      exact GeneralizationLifetime.binary_left inputs.ready inputs.wellFormed inputs.catalog
        inputs.bounds form allocation childAccepted rightRun accepted life
  | expression_binary_right accepted form allocation leftAccepted childAccepted =>
      exact GeneralizationLifetime.binary_right inputs.ready inputs.catalog inputs.bounds
        form allocation leftAccepted childAccepted accepted life
  | expression_conditional_condition accepted form allocation childAccepted =>
      obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult, elseState,
        unified, conditionRun, thenRun, elseRun, _⟩ :=
        inferExprFuel_success_conditional_facts form allocation accepted
      cases Except.ok.inj (conditionRun.symm.trans childAccepted)
      exact GeneralizationLifetime.conditional_condition inputs.ready inputs.wellFormed
        inputs.catalog inputs.bounds form allocation childAccepted thenRun elseRun accepted life
  | expression_conditional_then accepted form allocation conditionAccepted childAccepted =>
      obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult, elseState,
        unified, conditionRun, thenRun, elseRun, _⟩ :=
        inferExprFuel_success_conditional_facts form allocation accepted
      cases Except.ok.inj (conditionRun.symm.trans conditionAccepted)
      cases Except.ok.inj (thenRun.symm.trans childAccepted)
      exact GeneralizationLifetime.conditional_then inputs.ready inputs.wellFormed
        inputs.catalog inputs.bounds form allocation conditionAccepted childAccepted elseRun accepted life
  | expression_conditional_else accepted form allocation conditionAccepted thenAccepted childAccepted =>
      exact GeneralizationLifetime.conditional_else inputs.ready inputs.catalog inputs.bounds
        form allocation conditionAccepted thenAccepted childAccepted accepted life
  | @expression_lambda_body childFuel context source expected initial allocated final id value
      keyword sourceParameters annotation body boundParameters parameterTypes parameterState bodyState resultType bodyResult
      accepted form allocation parametersAccepted prefixFacts childAccepted =>
      obtain ⟨parameters, types, parameterState, resultType, resultState, bodyResult,
        unifiedState, restoredState, parametersRun, actualPrefix, bodyRun, unified, restored, recorded⟩ :=
        inferExprFuel_success_lambda_facts form allocation accepted
      cases Except.ok.inj (parametersRun.symm.trans parametersAccepted)
      obtain ⟨sameType, sameState⟩ := lambdaPrefix_unique actualPrefix prefixFacts
      cases sameType
      cases sameState
      cases Except.ok.inj (bodyRun.symm.trans childAccepted)
      exact GeneralizationLifetime.finishLambda (initial := initial) (context := context)
        (expression := source) (parameters := sourceParameters) (body := body)
        life inputs.ready inputs.catalog.catalog
        inputs.catalog.formation inputs.catalog.canonical inputs.bounds
        (by simpa only [allocation] using parametersAccepted) prefixFacts childAccepted unified
        (by simpa only [allocation] using restored)
        (by simpa only [allocation] using recorded)
  | expression_index_base accepted form allocation childAccepted =>
      obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState, mappingState,
        indexResult, indexState, baseRun, keyFresh, valueFresh, fitted, keyRun, _⟩ :=
        inferExprFuel_success_index_facts form allocation accepted
      cases Except.ok.inj (baseRun.symm.trans childAccepted)
      exact GeneralizationLifetime.index_base inputs.ready inputs.wellFormed inputs.catalog
        inputs.bounds form allocation childAccepted keyFresh valueFresh fitted keyRun accepted life
  | expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitted childAccepted =>
      exact GeneralizationLifetime.index_key inputs.ready inputs.catalog inputs.bounds
        form allocation baseAccepted keyFresh valueFresh fitted childAccepted accepted life
  | expression_call_arguments accepted form allocation nonconstructor childAccepted =>
      exact GeneralizationLifetime.call_arguments inputs.ready inputs.wellFormed inputs.catalog
        inputs.bounds form allocation nonconstructor childAccepted accepted life
  | expression_call_callee accepted form allocation nonconstructor argumentsAccepted indirect childAccepted =>
      exact GeneralizationLifetime.call_callee inputs.ready inputs.catalog inputs.bounds
        form allocation nonconstructor argumentsAccepted indirect childAccepted accepted life
  | @expression_call_constructor fuel context source expected initial allocated final id value
      callee arguments dataType constructor instantiation instantiated childFinal inferred
      accepted form allocation selected fresh childAccepted =>
      have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
      have sameNext : allocated.inference.next = initial.inference.next := by rw [same]; rfl
      obtain ⟨dataMember, constructorMember⟩ :=
        constructorCalleeCandidates_success_members selected dataType constructor (by simp)
      have properties := freshDataConstructorInstantiation_inferenceProperties dataType constructor
        allocated (same ▸ inputs.ready.allocateExpressionId)
        (inputs.catalog.formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember _)
      simp only [fresh] at properties
      have childRun := childAccepted
      change inferConstructorApplicationFuel fuel context source id instantiation
        arguments.elements expected instantiated = .ok (inferred, childFinal) at childRun
      have sameResult : (inferred, childFinal) = (value, final) := by
        change inferExprFuel (fuel + 1) context source expected initial = .ok (value, final) at accepted
        unfold inferExprFuel at accepted
        simp only [allocation, form, selected, fresh, childRun, bind, Except.bind] at accepted
        exact Except.ok.inj accepted
      cases sameResult
      exact life.weaken_entry (by simpa only [sameNext, CallIndex.initial] using properties.1.next_le)
  | @expression_contextual_constructor fuel context source expected initial allocated final id value
      dot name arguments dataType constructor typeArguments inferred childFinal
      accepted form allocation selected childAccepted =>
      have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
      have childRun := childAccepted
      change inferConstructorApplicationFuel fuel context source id
        (instantiateDataConstructor dataType constructor typeArguments)
        (arguments.map (·.elements) |>.getD []) expected allocated =
        .ok (inferred, childFinal) at childRun
      have sameResult : (inferred, childFinal) = (value, final) := by
        change inferExprFuel (fuel + 1) context source expected initial = .ok (value, final) at accepted
        unfold inferExprFuel at accepted
        simp only [allocation, form, selected, childRun, bind, Except.bind] at accepted
        exact Except.ok.inj accepted
      cases sameResult
      have sameNext : allocated.inference.next = initial.inference.next := by rw [same]; rfl
      simpa only [CallIndex.initial, CallIndex.final, CallIndex.outputTypes, sameNext] using life
  | @expression_field_constructor fuel context source expected initial allocated final id value
      base dot name dataType constructor instantiation instantiated childFinal inferred
      accepted form allocation selected fresh childAccepted =>
      have same : allocated = initial.allocateExpressionId.2 := (congrArg Prod.snd allocation).symm
      have sameNext : allocated.inference.next = initial.inference.next := by rw [same]; rfl
      obtain ⟨dataMember, constructorMember⟩ :=
        constructorCalleeCandidates_success_members selected dataType constructor (by simp)
      have properties := freshDataConstructorInstantiation_inferenceProperties dataType constructor
        allocated (same ▸ inputs.ready.allocateExpressionId)
        (inputs.catalog.formation.data_constructor_payloadTypes_variablesBelow dataMember constructorMember _)
      simp only [fresh] at properties
      have childRun := childAccepted
      change inferConstructorApplicationFuel fuel context source id instantiation [] expected
        instantiated = .ok (inferred, childFinal) at childRun
      have sameResult : (inferred, childFinal) = (value, final) := by
        change inferExprFuel (fuel + 1) context source expected initial = .ok (value, final) at accepted
        unfold inferExprFuel at accepted
        simp only [allocation, form, selected, fresh, childRun, bind, Except.bind] at accepted
        exact Except.ok.inj accepted
      cases sameResult
      exact life.weaken_entry (by simpa only [sameNext, CallIndex.initial] using properties.1.next_le)

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualExpressionSuffixProgress
/-! The remaining operator and call computation extends the inference state
returned by its actual child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness SourceInferenceSoundness.ProtectedVariables

theorem unary_suffix_progress
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.UnaryOp} {value : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (below : value.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (dispatch : UnaryExpressionDispatchFacts context source id operator value expected literals state result) :
    state.InferenceProgress result.2 := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferUnaryOperator context operator.value value.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.unary operator.value value.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      state.InferenceProgress result.2 := by
    have properties := inferUnaryOperator_inferenceProperties ready below expectedBelow accepted
    exact properties.1.trans (recordExpressionWithExpected_inferenceProperties
      properties.2.1 properties.2.2
      (fun type member => (expectedBelow type member).weaken properties.1.next_le) recorded).1
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt _ lookup selected recorded =>
      have cataloged := functionsNamed_success_subset_catalog lookup
      have properties := selectFunctionCandidateFrom_inferenceProperties ready
        (by intro argument member; cases List.mem_singleton.mp member; exact below)
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (cataloged member) (catalog.canonical signature (cataloged member)) _) expectedBelow selected
      let callee : Syntax.Expr := {
        span := operator.span
        value := .identifier {span := operator.span, value := name} }
      have after := recordSelectedCall_inferenceProperties source callee name [value] attempt
        properties.2.1 properties.2.2
      change recordSelectedCall source callee name [value] attempt = result at recorded
      rw [recorded] at after
      exact properties.1.trans after.1

theorem binary_suffix_progress
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.BinaryOp} {left right : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (leftBelow : left.type.VariablesBelow state.inference.next)
    (rightBelow : right.type.VariablesBelow state.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow state.inference.next)
    (dispatch : BinaryExpressionDispatchFacts context source id operator left right expected literals state result) :
    state.InferenceProgress result.2 := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferBinaryOperator context operator.value left.type right.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.binary left.id operator.value right.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      state.InferenceProgress result.2 := by
    have properties := inferBinaryOperator_inferenceProperties ready leftBelow rightBelow expectedBelow accepted
    exact properties.1.trans (recordExpressionWithExpected_inferenceProperties
      properties.2.1 properties.2.2
      (fun type member => (expectedBelow type member).weaken properties.1.next_le) recorded).1
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt fitted _ lookup selected fitting recorded =>
      have cataloged := functionsNamed_success_subset_catalog lookup
      have argumentsBelow : ∀ argument ∈ [left, right],
          argument.type.VariablesBelow state.inference.next := by
        intro argument member
        rcases List.mem_cons.mp member with rfl | member
        · exact leftBelow
        · cases List.mem_singleton.mp member
          exact rightBelow
      have boolBelow : ∀ type ∈ (some Ty.bool : Option Ty),
          type.VariablesBelow state.inference.next := by
        intro type member
        cases Option.some.inj (Option.mem_def.mp member)
        exact Ty.variablesBelow_constructor _ _
      have properties := selectFunctionCandidateFrom_inferenceProperties ready argumentsBelow
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (cataloged member) (catalog.canonical signature (cataloged member)) _) boolBelow selected
      have fittedProperties := withExpected_inferenceProperties properties.2.1 properties.2.2
        (fun type member => (expectedBelow type member).weaken properties.1.next_le) fitting
      let callee : Syntax.Expr := {
        span := operator.span
        value := .identifier {span := operator.span, value := name} }
      have after := recordSelectedCallResult_inferenceProperties source callee name [left, right]
        attempt fitted.expression fitted.coercions fitted.state fittedProperties.2.1 fittedProperties.2.2
      change recordSelectedCallResult source callee name [left, right] attempt
        fitted.expression fitted.coercions fitted.state = result at recorded
      rw [recorded] at after
      exact properties.1.trans (fittedProperties.1.trans after.1)

theorem call_arguments_suffix_progress
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (nonconstructor : constructorCalleeCandidates context initial callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements initial = .ok child)
    (dispatch : CallExpressionDispatchProvenanceFacts context source callee arguments id expected fuel initial result) :
    child.2.InferenceProgress result.2 := by
  have properties := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical childAccepted
  have expectedAfter : ∀ type ∈ expected, type.VariablesBelow child.2.inference.next :=
    fun type member => (expectedBelow type member).weaken properties.1.next_le
  cases dispatch with
  | constructor discovery _ _ => simp [nonconstructor] at discovery
  | @selected inferredArguments argumentState name candidates integerLiterals attempt _ actualArguments origin selected recorded =>
      cases Except.ok.inj (actualArguments.symm.trans childAccepted)
      have selectedProperties := selectFunctionCandidateFrom_inferenceProperties properties.2.1 properties.2.2
        (fun signature member => catalog.formation.function_scheme_body_variablesBelow
          (origin.candidatesSubset member) (catalog.canonical signature (origin.candidatesSubset member)) _)
        expectedAfter selected
      have after := recordSelectedCall_inferenceProperties source callee name inferredArguments attempt
        selectedProperties.2.1 selectedProperties.2.2
      rw [recorded] at after
      exact selectedProperties.1.trans after.1
  | builtin _ actualArguments recorded =>
      cases Except.ok.inj (actualArguments.symm.trans childAccepted)
      exact (recordBuiltinFunctionCall_inferenceProperties properties.2.1 properties.2.2 expectedAfter recorded).1
  | @indirect inferredArguments argumentState calleeState inferredCallee application _ actualArguments _ calleeAccepted applicationAccepted recorded =>
      cases Except.ok.inj (actualArguments.symm.trans childAccepted)
      have calleeProperties := inferExprFuel_inferenceProperties properties.2.1
        catalog.formation catalog.canonical (by simp) calleeAccepted
      have applicationProperties := applyFunctionType_inferenceProperties calleeProperties.2.1 calleeProperties.2.2
        (fun argument member => (properties.2.2 argument member).weaken calleeProperties.1.next_le)
        (fun type member => (expectedAfter type member).weaken calleeProperties.1.next_le) applicationAccepted
      have after := recordIndirectCall_inferenceProperties source inferredCallee inferredArguments application
        applicationProperties.2.1 applicationProperties.2.2
      rw [recorded] at after
      exact calleeProperties.1.trans (applicationProperties.1.trans after.1)

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualBranchSuffixProgress
/-! Actual branch, index and lambda continuations preserve the inference
substitution produced inside them. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness SourceInferenceSoundness.ProtectedVariables

theorem conditional_suffix_progress
    {fuel : Nat} {context : SourceInference.Context}
    {source condition thenBranch elseBranch : Syntax.Expr} {id : ExpressionId}
    {expected : Option Ty} {initial : State}
    {conditionResult thenResult elseResult result : InferredExpression × State}
    {unifiedState : State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (conditionRun : inferExprFuel fuel context condition (some .bool) initial = .ok conditionResult)
    (thenRun : inferExprFuel fuel context thenBranch expected conditionResult.2 = .ok thenResult)
    (elseRun : inferExprFuel fuel context elseBranch expected thenResult.2 = .ok elseResult)
    (unified : unify elseResult.2 thenResult.1.type elseResult.1.type = .ok unifiedState)
    (recorded : recordExpressionWithExpected context source id
      (unifiedState.resolve thenResult.1.type)
      (.conditional conditionResult.1.id thenResult.1.id elseResult.1.id) [] expected unifiedState = .ok result) :
    conditionResult.2.InferenceProgress result.2 ∧
      thenResult.2.InferenceProgress result.2 ∧ elseResult.2.InferenceProgress result.2 := by
  have boolBelow : ∀ type ∈ (some Ty.bool : Option Ty),
      type.VariablesBelow initial.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact Ty.variablesBelow_constructor _ _
  have conditionProperties := inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical boolBelow conditionRun
  have thenProperties := inferExprFuel_inferenceProperties conditionProperties.2.1 catalog.formation catalog.canonical
    (fun type member => (expectedBelow type member).weaken conditionProperties.1.next_le) thenRun
  have elseProperties := inferExprFuel_inferenceProperties thenProperties.2.1 catalog.formation catalog.canonical
    (fun type member => (expectedBelow type member).weaken (conditionProperties.1.trans thenProperties.1).next_le) elseRun
  have thenBelow := thenProperties.2.2.weaken elseProperties.1.next_le
  have unifiedProgress := unify_inferenceProgress elseProperties.2.1.solved thenBelow elseProperties.2.2 unified
  have unifiedReady := unify_preserves_inferenceReady elseProperties.2.1 thenBelow elseProperties.2.2 unified
  have recordedProgress := (recordExpressionWithExpected_inferenceProperties unifiedReady
    (unifiedReady.solved.variablesBelow_apply (thenBelow.weaken unifiedProgress.next_le))
    (fun type member => (expectedBelow type member).weaken
      (conditionProperties.1.trans (thenProperties.1.trans (elseProperties.1.trans unifiedProgress))).next_le)
    recorded).1
  have afterElse := unifiedProgress.trans recordedProgress
  exact ⟨thenProperties.1.trans (elseProperties.1.trans afterElse),
    elseProperties.1.trans afterElse, afterElse⟩

theorem index_suffix_progress
    {fuel : Nat} {context : SourceInference.Context} {source key : Syntax.Expr}
    {id : ExpressionId} {expected : Option Ty}
    {baseResult keyResult : InferredExpression}
    {baseState keyState valueState mappingState indexState : State}
    {keyType valueType : Ty} {result : InferredExpression × State}
    (ready : baseState.InferenceReady) (catalog : LifetimeInferenceContext context)
    (baseBelow : baseResult.type.VariablesBelow baseState.inference.next)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow baseState.inference.next)
    (keyFresh : baseState.fresh = (keyType, keyState))
    (valueFresh : keyState.fresh = (valueType, valueState))
    (mappingRun : unify valueState baseResult.type (.mapping keyType valueType) = .ok mappingState)
    (keyRun : inferExprFuel fuel context key (some (mappingState.resolve keyType)) mappingState =
      .ok (keyResult, indexState))
    (recorded : recordExpressionWithExpected context source id (indexState.resolve valueType)
      (.index baseResult.id keyResult.id) [] expected indexState = .ok result) :
    baseState.InferenceProgress result.2 ∧ indexState.InferenceProgress result.2 := by
  have keyProperties := fresh_eq_inferenceProperties ready keyFresh
  have valueProperties := fresh_eq_inferenceProperties keyProperties.2.1 valueFresh
  have baseBelow := baseBelow.weaken (keyProperties.1.trans valueProperties.1).next_le
  have keyBelow := keyProperties.2.2.weaken valueProperties.1.next_le
  have mappingBelow := (Ty.variablesBelow_mapping_iff _ _ _).2 ⟨keyBelow, valueProperties.2.2⟩
  have mappingProgress := unify_inferenceProgress valueProperties.2.1.solved baseBelow mappingBelow mappingRun
  have mappingReady := unify_preserves_inferenceReady valueProperties.2.1 baseBelow mappingBelow mappingRun
  have expectedKey : ∀ type ∈ (some (mappingState.resolve keyType) : Option Ty),
      type.VariablesBelow mappingState.inference.next := by
    intro type member
    cases Option.some.inj (Option.mem_def.mp member)
    exact mappingReady.solved.variablesBelow_apply (keyBelow.weaken mappingProgress.next_le)
  have indexProperties := inferExprFuel_inferenceProperties mappingReady catalog.formation catalog.canonical expectedKey keyRun
  have valueBelow := valueProperties.2.2.weaken (mappingProgress.trans indexProperties.1).next_le
  have beforeRecord := keyProperties.1.trans (valueProperties.1.trans (mappingProgress.trans indexProperties.1))
  have recordedProgress := (recordExpressionWithExpected_inferenceProperties indexProperties.2.1
    (indexProperties.2.1.solved.variablesBelow_apply valueBelow)
    (fun type member => (expectedBelow type member).weaken beforeRecord.next_le) recorded).1
  exact ⟨beforeRecord.trans recordedProgress, recordedProgress⟩

theorem lambda_suffix_progress
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {parameters : Syntax.DelimitedList Syntax.LambdaParameter} {annotation : Option Syntax.TypeExpr}
    {body : Syntax.Block} {expected : Option Ty} {initial : State}
    {boundParameters : List TypedBinder} {parameterTypes : List Ty} {parameterState : State}
    {resultType : Ty} {bodyState : State} {bodyResult : BlockResult}
    {unifiedState restoredState : State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (parametersRun : bindLambdaParameters context parameters.elements 0 []
      initial.allocateExpressionId.2 = .ok (boundParameters, parameterTypes, parameterState))
    (prefixFacts : LambdaPrefixFacts context expected annotation parameterTypes parameterState resultType bodyState)
    (bodyRun : inferStatementsFuel childFuel {context with loopDepth := 0}
      body.value resultType bodyState = .ok bodyResult)
    (unified : unify bodyResult.state bodyResult.type resultType = .ok unifiedState)
    (restored : restoredState = unifiedState.restoreLexicalScope initial.allocateExpressionId.2.lexicalScope)
    (recorded : recordExpressionWithExpected context source initial.allocateExpressionId.1
      (.function (restoredState.resolve (Ty.productMany parameterTypes)) (restoredState.resolve resultType))
      (.lambda boundParameters (restoredState.resolve resultType) bodyResult.statements)
      [] expected restoredState = .ok result) :
    bodyResult.state.InferenceProgress result.2 := by
  have allocation : initial.InferenceProgress initial.allocateExpressionId.2 :=
    .allocateExpressionId initial ready.solved
  have parametersProperties := bindLambdaParameters_inferenceProperties ready.allocateExpressionId parametersRun
  have parameterBelow := Ty.variablesBelow_productMany parametersProperties.2.2
  have initialToParameter := allocation.trans parametersProperties.1
  have prefixProperties := lambdaPrefixFacts_inferenceProperties prefixFacts parametersProperties.2.1
    parameterBelow (fun type member => (expectedBelow type member).weaken initialToParameter.next_le)
  have bodyProperties := inferStatementsFuel_inferenceProperties
    (context := {context with loopDepth := 0}) prefixProperties.2.1 catalog.formation catalog.canonical
    prefixProperties.2.2 bodyRun
  have unifiedProgress := unify_inferenceProgress bodyProperties.2.1.solved bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have unifiedReady := unify_preserves_inferenceReady bodyProperties.2.1 bodyProperties.2.2
    (prefixProperties.2.2.weaken bodyProperties.1.next_le) unified
  have parametersToUnified := prefixProperties.1.trans (bodyProperties.1.trans unifiedProgress)
  have restoredProperties := State.restoreLexicalScope_inferenceProperties ready.allocateExpressionId
    (parametersProperties.1.trans parametersToUnified)
  subst restoredState
  have restoreProgress : unifiedState.InferenceProgress
      (unifiedState.restoreLexicalScope initial.allocateExpressionId.2.lexicalScope) :=
    .restoreLexicalScope _ _ unifiedReady.solved
  have parametersToRestored := parametersToUnified.trans restoreProgress
  have bodyEntryToRestored := bodyProperties.1.trans (unifiedProgress.trans restoreProgress)
  have recordedProgress := (recordExpressionWithExpected_inferenceProperties restoredProperties.2
    ((Ty.variablesBelow_function_iff _ _ _).mpr
      ⟨parametersToRestored.resolve_variablesBelow parameterBelow,
        bodyEntryToRestored.resolve_variablesBelow prefixProperties.2.2⟩)
    (fun type member => (expectedBelow type member).weaken (allocation.trans restoredProperties.1).next_le)
    recorded).1
  exact unifiedProgress.trans (restoreProgress.trans recordedProgress)

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualExpressionProgress
/-! Each actual expression child returns an inference state extended by
the remainder of the same parent computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness SourceInferenceSoundness.ProtectedVariables

private theorem allocation_next {initial allocated : State} {id : ExpressionId}
    (allocation : initial.allocateExpressionId = (id, allocated)) :
    allocated.inference.next = initial.inference.next := by
  rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocation]
  rfl

private theorem allocation_ready {initial allocated : State} {id : ExpressionId}
    (ready : initial.InferenceReady)
    (allocation : initial.allocateExpressionId = (id, allocated)) : allocated.InferenceReady := by
  rw [← show initial.allocateExpressionId.2 = allocated from congrArg Prod.snd allocation]
  exact ready.allocateExpressionId

theorem ChildStep.progress_expression
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial final : State} {value : InferredExpression}
    {child : CallIndex}
    (inputs : (CallIndex.expression fuel context source expected initial value final).Inputs)
    (step : ChildStep (.expression fuel context source expected initial value final) child) :
    child.final.InferenceProgress final := by
  have childProperties := (step.inputs inputs).progress step.child_accepted
  cases step with
  | expression_group accepted form allocation childAccepted =>
      obtain ⟨innerResult, innerState, innerRun, recorded⟩ :=
        Detail.inferExprFuel_success_group_facts form allocation accepted
      cases Except.ok.inj (innerRun.symm.trans childAccepted)
      exact (recordExpressionWithExpected_inferenceProperties childProperties.2.1
        (childProperties.2.2 _ (by simp [CallIndex.outputTypes]))
        (fun type member => ((allocation_next allocation) ▸ inputs.bounds type member).weaken childProperties.1.next_le)
        recorded).1
  | expression_tuple accepted form allocation childAccepted =>
      obtain ⟨elements, elementState, elementsRun, recorded⟩ :=
        inferExprFuel_success_tuple_facts form allocation accepted
      cases Except.ok.inj (elementsRun.symm.trans childAccepted)
      have productBelow := Ty.variablesBelow_productMany childProperties.2.2
      exact (recordExpressionWithExpected_inferenceProperties childProperties.2.1 productBelow
        (fun type member => ((allocation_next allocation) ▸ inputs.bounds type member).weaken childProperties.1.next_le)
        recorded).1
  | expression_unary accepted form allocation childAccepted =>
      obtain ⟨operand, operandState, operandRun, dispatch⟩ :=
        inferExprFuel_success_unary_facts form allocation accepted
      cases Except.ok.inj (operandRun.symm.trans childAccepted)
      exact unary_suffix_progress childProperties.2.1 inputs.catalog
        (childProperties.2.2 _ (by simp [CallIndex.outputTypes]))
        (fun type member => ((allocation_next allocation) ▸ inputs.bounds type member).weaken childProperties.1.next_le)
        dispatch
  | expression_binary_left accepted form allocation childAccepted =>
      obtain ⟨leftResult, leftState, rightResult, rightState, leftRun, rightRun, dispatch⟩ :=
        inferExprFuel_success_binary_facts form allocation accepted
      cases Except.ok.inj (leftRun.symm.trans childAccepted)
      have rightProperties := inferExprFuel_inferenceProperties childProperties.2.1
        inputs.catalog.formation inputs.catalog.canonical (by simp) rightRun
      exact rightProperties.1.trans (binary_suffix_progress rightProperties.2.1 inputs.catalog
        ((childProperties.2.2 _ (by simp [CallIndex.outputTypes])).weaken rightProperties.1.next_le)
        rightProperties.2.2
        (fun type member => ((allocation_next allocation) ▸ inputs.bounds type member).weaken
          (childProperties.1.trans rightProperties.1).next_le) dispatch)
  | expression_binary_right accepted form allocation leftAccepted childAccepted =>
      obtain ⟨leftResult, leftState, rightResult, rightState, leftRun, rightRun, dispatch⟩ :=
        inferExprFuel_success_binary_facts form allocation accepted
      cases Except.ok.inj (leftRun.symm.trans leftAccepted)
      cases Except.ok.inj (rightRun.symm.trans childAccepted)
      have allocatedReady := allocation_ready inputs.ready allocation
      have leftProperties := inferExprFuel_inferenceProperties allocatedReady
        inputs.catalog.formation inputs.catalog.canonical (by simp) leftAccepted
      exact binary_suffix_progress childProperties.2.1 inputs.catalog
        (leftProperties.2.2.weaken childProperties.1.next_le)
        (childProperties.2.2 _ (by simp [CallIndex.outputTypes]))
        (fun type member => ((allocation_next allocation) ▸ inputs.bounds type member).weaken
          (leftProperties.1.trans childProperties.1).next_le) dispatch
  | expression_conditional_condition accepted form allocation childAccepted =>
      obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult, elseState,
        unified, conditionRun, thenRun, elseRun, unification, recorded⟩ :=
        inferExprFuel_success_conditional_facts form allocation accepted
      cases Except.ok.inj (conditionRun.symm.trans childAccepted)
      exact (conditional_suffix_progress
        (allocation_ready inputs.ready allocation) inputs.catalog
        (fun type member => (allocation_next allocation) ▸ inputs.bounds type member)
        childAccepted thenRun elseRun unification recorded).1
  | expression_conditional_then accepted form allocation conditionAccepted childAccepted =>
      obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult, elseState,
        unified, conditionRun, thenRun, elseRun, unification, recorded⟩ :=
        inferExprFuel_success_conditional_facts form allocation accepted
      cases Except.ok.inj (conditionRun.symm.trans conditionAccepted)
      cases Except.ok.inj (thenRun.symm.trans childAccepted)
      exact (conditional_suffix_progress
        (allocation_ready inputs.ready allocation) inputs.catalog
        (fun type member => (allocation_next allocation) ▸ inputs.bounds type member)
        conditionAccepted childAccepted elseRun unification recorded).2.1
  | expression_conditional_else accepted form allocation conditionAccepted thenAccepted childAccepted =>
      obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult, elseState,
        unified, conditionRun, thenRun, elseRun, unification, recorded⟩ :=
        inferExprFuel_success_conditional_facts form allocation accepted
      cases Except.ok.inj (conditionRun.symm.trans conditionAccepted)
      cases Except.ok.inj (thenRun.symm.trans thenAccepted)
      cases Except.ok.inj (elseRun.symm.trans childAccepted)
      exact (conditional_suffix_progress
        (allocation_ready inputs.ready allocation) inputs.catalog
        (fun type member => (allocation_next allocation) ▸ inputs.bounds type member)
        conditionAccepted thenAccepted childAccepted unification recorded).2.2
  | @expression_lambda_body childFuel context source expected initial allocated final id value
      keyword sourceParameters annotation body boundParameters parameterTypes parameterState bodyState resultType bodyResult
      accepted form allocation parametersAccepted prefixFacts childAccepted =>
      obtain ⟨parameters, types, parameterState, resultType, resultState, bodyResult,
        unifiedState, restoredState, parametersRun, actualPrefix, bodyRun, unified, restored, recorded⟩ :=
        inferExprFuel_success_lambda_facts form allocation accepted
      cases Except.ok.inj (parametersRun.symm.trans parametersAccepted)
      obtain ⟨sameType, sameState⟩ := lambdaPrefix_unique actualPrefix prefixFacts
      cases sameType
      cases sameState
      cases Except.ok.inj (bodyRun.symm.trans childAccepted)
      exact lambda_suffix_progress (initial := initial) (context := context)
        (source := source) (parameters := sourceParameters) (body := body)
        inputs.ready inputs.catalog inputs.bounds
        (by simpa only [allocation] using parametersAccepted) prefixFacts childAccepted unified
        (by simpa only [allocation] using restored)
        (by simpa only [allocation] using recorded)
  | expression_index_base accepted form allocation childAccepted =>
      obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState, mappingState,
        indexResult, indexState, baseRun, keyFresh, valueFresh, fitted, keyRun, recorded⟩ :=
        inferExprFuel_success_index_facts form allocation accepted
      cases Except.ok.inj (baseRun.symm.trans childAccepted)
      exact (index_suffix_progress childProperties.2.1 inputs.catalog
        (childProperties.2.2 _ (by simp [CallIndex.outputTypes]))
        (fun type member => ((allocation_next allocation) ▸ inputs.bounds type member).weaken childProperties.1.next_le)
        keyFresh valueFresh fitted keyRun recorded).1
  | expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitted childAccepted =>
      obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState, mappingState,
        indexResult, indexState, baseRun, actualKeyFresh, actualValueFresh, actualFitted, keyRun, recorded⟩ :=
        inferExprFuel_success_index_facts form allocation accepted
      cases Except.ok.inj (baseRun.symm.trans baseAccepted)
      cases actualKeyFresh.symm.trans keyFresh
      cases actualValueFresh.symm.trans valueFresh
      cases Except.ok.inj (actualFitted.symm.trans fitted)
      cases Except.ok.inj (keyRun.symm.trans childAccepted)
      have baseProperties := inferExprFuel_inferenceProperties
        (allocation_ready inputs.ready allocation)
        inputs.catalog.formation inputs.catalog.canonical (by simp) baseAccepted
      exact (index_suffix_progress baseProperties.2.1 inputs.catalog baseProperties.2.2
        (fun type member => ((allocation_next allocation) ▸ inputs.bounds type member).weaken baseProperties.1.next_le)
        keyFresh valueFresh fitted childAccepted recorded).2
  | expression_call_arguments accepted form allocation nonconstructor childAccepted =>
      exact call_arguments_suffix_progress
        (allocation_ready inputs.ready allocation) inputs.catalog
        (fun type member => (allocation_next allocation) ▸ inputs.bounds type member)
        nonconstructor childAccepted (inferExprFuel_success_call_dispatch_provenance_facts form allocation accepted)
  | @expression_call_callee fuel context source expected initial allocated final id value
      callee arguments values argumentState childFinal inferred
      accepted form allocation nonconstructor argumentsAccepted indirect childAccepted =>
      obtain ⟨application, applicationRun, recorded⟩ :=
        indirectCall_actual_suffix form allocation nonconstructor argumentsAccepted indirect childAccepted accepted
      have argumentsProperties := inferExprsFuel_inferenceProperties
        (allocation_ready inputs.ready allocation)
        inputs.catalog.formation inputs.catalog.canonical argumentsAccepted
      have applicationProperties := applyFunctionType_inferenceProperties childProperties.2.1
        (childProperties.2.2 _ (by simp [CallIndex.outputTypes]))
        (fun argument member => (argumentsProperties.2.2 argument member).weaken childProperties.1.next_le)
        (fun type member => ((allocation_next allocation) ▸ inputs.bounds type member).weaken
          (argumentsProperties.1.trans childProperties.1).next_le) applicationRun
      have after := recordIndirectCall_inferenceProperties source inferred values application
        applicationProperties.2.1 applicationProperties.2.2
      rw [recorded] at after
      exact applicationProperties.1.trans after.1
  | @expression_call_constructor fuel context source expected initial allocated final id value
      callee arguments dataType constructor instantiation instantiated childFinal inferred
      accepted form allocation selected fresh childAccepted =>
      change inferConstructorApplicationFuel fuel context source id instantiation
        arguments.elements expected instantiated = .ok (inferred, childFinal) at childAccepted
      have same : (inferred, childFinal) = (value, final) := by
        change inferExprFuel (fuel + 1) context source expected initial = .ok (value, final) at accepted
        unfold inferExprFuel at accepted
        simp only [allocation, form, selected, fresh, childAccepted, bind, Except.bind] at accepted
        exact Except.ok.inj accepted
      cases same
      exact .refl childProperties.2.1.solved
  | @expression_contextual_constructor fuel context source expected initial allocated final id value
      dot name arguments dataType constructor typeArguments inferred childFinal
      accepted form allocation selected childAccepted =>
      change inferConstructorApplicationFuel fuel context source id
        (instantiateDataConstructor dataType constructor typeArguments)
        (arguments.map (·.elements) |>.getD []) expected allocated =
        .ok (inferred, childFinal) at childAccepted
      have same : (inferred, childFinal) = (value, final) := by
        change inferExprFuel (fuel + 1) context source expected initial = .ok (value, final) at accepted
        unfold inferExprFuel at accepted
        simp only [allocation, form, selected, childAccepted, bind, Except.bind] at accepted
        exact Except.ok.inj accepted
      cases same
      exact .refl childProperties.2.1.solved
  | @expression_field_constructor fuel context source expected initial allocated final id value
      base dot name dataType constructor instantiation instantiated childFinal inferred
      accepted form allocation selected fresh childAccepted =>
      change inferConstructorApplicationFuel fuel context source id instantiation [] expected
        instantiated = .ok (inferred, childFinal) at childAccepted
      have same : (inferred, childFinal) = (value, final) := by
        change inferExprFuel (fuel + 1) context source expected initial = .ok (value, final) at accepted
        unfold inferExprFuel at accepted
        simp only [allocation, form, selected, fresh, childAccepted, bind, Except.bind] at accepted
        exact Except.ok.inj accepted
      cases same
      exact .refl childProperties.2.1.solved

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualSuffixProgress
/-! Each actual child result reaches the final inference state of its root call.
This composes accepted child computations and never assumes final substitution
agreement for an intermediate state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem ChildStep.suffixProgress {parent child : CallIndex}
    (inputs : parent.Inputs) (step : ChildStep parent child) :
    child.final.InferenceProgress parent.final := by
  cases parent <;> first
  | exact step.progress_expression inputs
  | exact step.progress_nonexpression inputs (by trivial)

theorem CallOccurrence.suffixProgress {root call : CallIndex}
    (here : CallOccurrence root call) (inputs : root.Inputs) :
    call.final.InferenceProgress root.final := by
  induction here with
  | root accepted => exact .refl ((inputs.progress accepted).2.1.solved)
  | child prior step ih => exact (step.suffixProgress (prior.inputs inputs)).trans ih

theorem CallOccurrence.final_extension {root call : CallIndex}
    (here : CallOccurrence root call) (inputs : root.Inputs) :
    root.final.inference.substitution.SemanticallyExtends call.final.inference.substitution :=
  (here.suffixProgress inputs).substitution_extends

end Solcore.SourceSemantics.SourceInferenceExecution
end
