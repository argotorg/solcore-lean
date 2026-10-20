import Solcore.SourceSemantics.SourceInferenceActualBranchSuffixProgress

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

private theorem lambdaPrefix_unique
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial : State}
    {leftType rightType : Ty} {leftState rightState : State}
    (left : LambdaPrefixFacts context expected annotation types initial leftType leftState)
    (right : LambdaPrefixFacts context expected annotation types initial rightType rightState) :
    leftType = rightType ∧ leftState = rightState := by
  cases left <;> cases right <;> simp_all

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
