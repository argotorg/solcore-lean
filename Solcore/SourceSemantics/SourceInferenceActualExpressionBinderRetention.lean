import Solcore.SourceSemantics.SourceInferenceActualOperatorBinderRetention
import Solcore.SourceSemantics.SourceInferenceActualIndirectCallPrefix

/-! Initialized declarations created by an actual expression child survive
the parent's remaining inference, including overloaded argument coercions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness
open LocalGeneralizationEvents (BindersRetained)

private theorem lambdaPrefix_unique
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial : State}
    {leftType rightType : Ty} {leftState rightState : State}
    (left : LambdaPrefixFacts context expected annotation types initial leftType leftState)
    (right : LambdaPrefixFacts context expected annotation types initial rightType rightState) :
    leftType = rightType ∧ leftState = rightState := by
  cases left <;> cases right <;> simp_all

theorem ChildStep.expression_binders_retained
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
    {expected : Option Ty} {initial final : State} {value : InferredExpression}
    {child : CallIndex}
    (step : ChildStep (.expression fuel context source expected initial value final) child) :
    BindersRetained child.final.nodes final.nodes := by
  cases step with
  | expression_group accepted form allocation childAccepted =>
    obtain ⟨innerResult, innerState, innerRun, recorded⟩ :=
      Detail.inferExprFuel_success_group_facts form allocation accepted
    cases Except.ok.inj (innerRun.symm.trans childAccepted)
    exact BindersRetained.recordExpressionWithExpected recorded
  | expression_tuple accepted form allocation childAccepted =>
    obtain ⟨elements, elementState, elementsRun, recorded⟩ :=
      inferExprFuel_success_tuple_facts form allocation accepted
    cases Except.ok.inj (elementsRun.symm.trans childAccepted)
    exact BindersRetained.recordExpressionWithExpected recorded
  | expression_unary accepted form allocation childAccepted =>
    obtain ⟨operand, operandState, operandRun, dispatch⟩ :=
      inferExprFuel_success_unary_facts form allocation accepted
    cases Except.ok.inj (operandRun.symm.trans childAccepted)
    exact ActualBinderRetention.unary dispatch
  | expression_binary_left accepted form allocation childAccepted =>
    obtain ⟨leftResult, leftState, rightResult, rightState, leftRun, rightRun, dispatch⟩ :=
      inferExprFuel_success_binary_facts form allocation accepted
    cases Except.ok.inj (leftRun.symm.trans childAccepted)
    exact (LocalGeneralizationEvents.inferExprFuel_origins_progress rightRun).retained.trans
      (ActualBinderRetention.binary dispatch)
  | expression_binary_right accepted form allocation leftAccepted childAccepted =>
    obtain ⟨leftResult, leftState, rightResult, rightState, leftRun, rightRun, dispatch⟩ :=
      inferExprFuel_success_binary_facts form allocation accepted
    cases Except.ok.inj (leftRun.symm.trans leftAccepted)
    cases Except.ok.inj (rightRun.symm.trans childAccepted)
    exact ActualBinderRetention.binary dispatch
  | expression_conditional_condition accepted form allocation childAccepted =>
    obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult, elseState,
      unified, conditionRun, thenRun, elseRun, unification, recorded⟩ :=
      inferExprFuel_success_conditional_facts form allocation accepted
    cases Except.ok.inj (conditionRun.symm.trans childAccepted)
    exact (LocalGeneralizationEvents.inferExprFuel_origins_progress thenRun).retained.trans
      ((LocalGeneralizationEvents.inferExprFuel_origins_progress elseRun).retained.trans
        ((LocalGeneralizationEvents.Progress.unify unification).retained.trans
          (BindersRetained.recordExpressionWithExpected recorded)))
  | expression_conditional_then accepted form allocation conditionAccepted childAccepted =>
    obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult, elseState,
      unified, conditionRun, thenRun, elseRun, unification, recorded⟩ :=
      inferExprFuel_success_conditional_facts form allocation accepted
    cases Except.ok.inj (conditionRun.symm.trans conditionAccepted)
    cases Except.ok.inj (thenRun.symm.trans childAccepted)
    exact (LocalGeneralizationEvents.inferExprFuel_origins_progress elseRun).retained.trans
      ((LocalGeneralizationEvents.Progress.unify unification).retained.trans
        (BindersRetained.recordExpressionWithExpected recorded))
  | expression_conditional_else accepted form allocation conditionAccepted thenAccepted childAccepted =>
    obtain ⟨conditionResult, conditionState, thenResult, thenState, elseResult, elseState,
      unified, conditionRun, thenRun, elseRun, unification, recorded⟩ :=
      inferExprFuel_success_conditional_facts form allocation accepted
    cases Except.ok.inj (conditionRun.symm.trans conditionAccepted)
    cases Except.ok.inj (thenRun.symm.trans thenAccepted)
    cases Except.ok.inj (elseRun.symm.trans childAccepted)
    exact (LocalGeneralizationEvents.Progress.unify unification).retained.trans
      (BindersRetained.recordExpressionWithExpected recorded)
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
    subst restoredState
    exact (LocalGeneralizationEvents.Progress.unify unified).retained.trans
      (BindersRetained.recordExpressionWithExpected recorded)
  | expression_index_base accepted form allocation childAccepted =>
    obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState, mappingState,
      indexResult, indexState, baseRun, keyFresh, valueFresh, fitted, keyRun, recorded⟩ :=
      inferExprFuel_success_index_facts form allocation accepted
    have keyNodes : keyState.nodes = baseState.nodes :=
      (congrArg (fun output : Ty × State => output.2.nodes) keyFresh).symm
    have valueNodes : valueState.nodes = keyState.nodes :=
      (congrArg (fun output : Ty × State => output.2.nodes) valueFresh).symm
    cases Except.ok.inj (baseRun.symm.trans childAccepted)
    have kept := (LocalGeneralizationEvents.Progress.unify fitted).retained.trans
      ((LocalGeneralizationEvents.inferExprFuel_origins_progress keyRun).retained.trans
        (BindersRetained.recordExpressionWithExpected recorded))
    simpa only [CallIndex.final, valueNodes, keyNodes] using kept
  | expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitted childAccepted =>
    obtain ⟨baseResult, baseState, keyType, keyState, valueType, valueState, mappingState,
      indexResult, indexState, baseRun, actualKeyFresh, actualValueFresh, actualFitted, keyRun, recorded⟩ :=
      inferExprFuel_success_index_facts form allocation accepted
    cases Except.ok.inj (baseRun.symm.trans baseAccepted)
    cases actualKeyFresh.symm.trans keyFresh
    cases actualValueFresh.symm.trans valueFresh
    cases Except.ok.inj (actualFitted.symm.trans fitted)
    cases Except.ok.inj (keyRun.symm.trans childAccepted)
    exact BindersRetained.recordExpressionWithExpected recorded
  | expression_call_arguments accepted form allocation nonconstructor childAccepted =>
    exact ActualBinderRetention.callArguments nonconstructor childAccepted
      (inferExprFuel_success_call_dispatch_provenance_facts form allocation accepted)
  | @expression_call_callee fuel context source expected initial allocated final id value
      callee arguments values argumentState childFinal inferred
      accepted form allocation nonconstructor argumentsAccepted indirect childAccepted =>
    obtain ⟨application, applicationRun, recorded⟩ :=
      indirectCall_actual_suffix form allocation nonconstructor argumentsAccepted indirect childAccepted accepted
    have after := (LocalGeneralizationEvents.Progress.recordIndirectCall source inferred values application).retained
    rw [recorded] at after
    exact (LocalGeneralizationEvents.Progress.applyFunctionType applicationRun).retained.trans after
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
    exact .refl _
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
    exact .refl _
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
    exact .refl _

end Solcore.SourceSemantics.SourceInferenceExecution
