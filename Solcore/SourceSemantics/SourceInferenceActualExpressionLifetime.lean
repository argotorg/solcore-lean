import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeExpressionSteps
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeUnary
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeBinary
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeIndex
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeConditional
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeCallSteps
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeLambda

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
