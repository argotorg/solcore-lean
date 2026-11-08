import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.SourceSemantics.Internal.Inference.Soundness
import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.Internal.Inference.ExpressionRetained
import Solcore.Frontend.SourceInference.Internal.LocalGeneralization
import Solcore.SourceSemantics.Internal.Execution.CallInputs
import Solcore.Frontend.SourceInference.Internal.Continuations
import Solcore.SourceSemantics.Internal.Execution.StatementProgress
import Solcore.SourceSemantics.Internal.Privacy.Active
import Solcore.Frontend.SourceInference.Internal.LocalGeneralizationBounds
import Solcore.SourceSemantics.Internal.Execution.GeneralizationEvents

/-!
# Binder retention

Initialized binders survive the rest of a parent, and capture origins follow each child entry.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualReturnedBindings
/-! Header declarations are returned before their enclosing loop records them.
This inventory follows those actual returned forms into the parent's source. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

/-- Initialized header declarations pending insertion into a statement node. -/
def CallIndex.returnedBindings : CallIndex → List InitializedLetBinding
  | .forItem _ _ _ _ item _ => forItemInitializedLetBindings item
  | .forItems _ _ _ _ result => result.items.flatMap forItemInitializedLetBindings
  | _ => []

private theorem forItems_result
    {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.ForItem} {sources : List Syntax.ForItem}
    {initial middle : State} {result : InferredForItems} {head : ForItemForm}
    (accepted : inferForItemsFuel fuel context (source :: sources) initial = .ok result)
    (first : inferForItemFuel fuel context source initial = .ok (head, middle)) :
    ∃ tail, inferForItemsFuel fuel context sources middle = .ok tail ∧
      result.items = head :: tail.items := by
  unfold inferForItemsFuel at accepted
  simp only [first, bind, Except.bind] at accepted
  cases rest : inferForItemsFuel fuel context sources middle with
  | error e => simp [rest, bind, Except.bind] at accepted
  | ok tail =>
    simp only [rest, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact ⟨tail, rfl, rfl⟩

/-- A child header's returned declaration is either still returned by its
parent header sequence, or has been recorded by its actual enclosing loop. -/
theorem ChildStep.returned_bindings {parent child : CallIndex}
    (step : ChildStep parent child) :
    child.returnedBindings ⊆
      initializedLetBindings (parent.final.toTypedSource []) ++ parent.returnedBindings := by
  cases step with
  | forItems_head accepted first =>
    obtain ⟨tail, _, items⟩ := forItems_result accepted first
    intro binding member
    apply List.mem_append_right
    simpa only [CallIndex.returnedBindings, items, List.flatMap_cons] using
      (List.mem_append_left (tail.items.flatMap forItemInitializedLetBindings) member)
  | forItems_tail accepted first rest =>
    obtain ⟨tail, tailAccepted, items⟩ := forItems_result accepted first
    have same := Except.ok.inj (tailAccepted.symm.trans rest)
    subst tail
    intro binding member
    apply List.mem_append_right
    simp only [CallIndex.returnedBindings, items, List.flatMap_cons]
    exact List.mem_append_right _ member
  | statement_for_initializer accepted form allocation initAccepted =>
    obtain ⟨init, test, testState, body, post, initRun, _, _, _, resultEq, _⟩ :=
      SourceInferenceSoundness.inferStatementFuel_success_forLoop_facts form allocation accepted
    have same := Except.ok.inj (initRun.symm.trans initAccepted)
    subst init
    intro binding member
    apply List.mem_append_left
    simp only [CallIndex.final, resultEq, initializedLetBindings, State.toTypedSource,
      State.recordNode, State.restoreLexicalScope, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, statementInitializedLetBindings]
    exact List.mem_append_right _ (List.mem_append_left _ member)
  | statement_for_post accepted form allocation initAccepted testAccepted bodyAccepted postAccepted =>
    obtain ⟨init, test, testState, body, post, initRun, testRun, bodyRun, postRun, resultEq, _⟩ :=
      SourceInferenceSoundness.inferStatementFuel_success_forLoop_facts form allocation accepted
    have same := Except.ok.inj (initRun.symm.trans initAccepted)
    subst init
    have same := Except.ok.inj (testRun.symm.trans testAccepted)
    cases same
    have same := Except.ok.inj (bodyRun.symm.trans bodyAccepted)
    subst body
    have same := Except.ok.inj (postRun.symm.trans postAccepted)
    subst post
    intro binding member
    apply List.mem_append_left
    simp only [CallIndex.final, resultEq, initializedLetBindings, State.toTypedSource,
      State.recordNode, State.restoreLexicalScope, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, statementInitializedLetBindings]
    exact List.mem_append_right _ (List.mem_append_right _ member)
  | _ => exact List.nil_subset _

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCaptureRetention
/-! The final body retains both recorded declarations and pending header items. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference

structure CallIndex.CaptureRetained (call : CallIndex) (whole : TypedSource) : Prop where
  nodes : (call.final.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders
  returned : ∀ binding ∈ call.returnedBindings, binding.binder ∈ whole.initializedLetBinders

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualOperatorBinderRetention
/-! Operator resolution and call recording preserve initialized declarations,
including when they attach coercions to argument expressions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualBinderRetention
open Frontend SourceInference TypeSystem Detail
open SourceInferenceSoundness
open LocalGeneralizationEvents (BindersRetained)

theorem unary
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.UnaryOp} {value : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (dispatch : UnaryExpressionDispatchFacts context source id operator value expected literals state result) :
    BindersRetained state.nodes result.2.nodes := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferUnaryOperator context operator.value value.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.unary operator.value value.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      BindersRetained state.nodes result.2.nodes :=
    (LocalGeneralizationEvents.Progress.inferUnaryOperator accepted).retained.trans
      (BindersRetained.recordExpressionWithExpected recorded)
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt _ lookup selected recorded =>
    let callee : Syntax.Expr := {
      span := operator.span
      value := .identifier {span := operator.span, value := name} }
    have after := (LocalGeneralizationEvents.Progress.recordSelectedCall source callee name [value] attempt).retained
    change recordSelectedCall source callee name [value] attempt = result at recorded
    rw [recorded] at after
    exact (LocalGeneralizationEvents.Progress.selectFunctionCandidateFrom selected).retained.trans after

theorem binary
    {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
    {operator : Syntax.Located Syntax.BinaryOp} {left right : InferredExpression}
    {expected : Option Ty} {literals : List IntegerLiteralOrigin} {state : State}
    {result : InferredExpression × State}
    (dispatch : BinaryExpressionDispatchFacts context source id operator left right expected literals state result) :
    BindersRetained state.nodes result.2.nodes := by
  have finish (operatorResult : OperatorInferenceResult)
      (accepted : inferBinaryOperator context operator.value left.type right.type expected literals state = .ok operatorResult)
      (recorded : recordExpressionWithExpected context source id operatorResult.type
        (.binary left.id operator.value right.id) operatorResult.requirements expected operatorResult.state = .ok result) :
      BindersRetained state.nodes result.2.nodes :=
    (LocalGeneralizationEvents.Progress.inferBinaryOperator accepted).retained.trans
      (BindersRetained.recordExpressionWithExpected recorded)
  cases dispatch with
  | directFunction _ _ accepted recorded => exact finish _ accepted recorded
  | traitMethod _ accepted recorded => exact finish _ accepted recorded
  | @selectedFunction name head tail attempt fitted _ lookup selected fitting recorded =>
    let callee : Syntax.Expr := {
      span := operator.span
      value := .identifier {span := operator.span, value := name} }
    have after := BindersRetained.recordSelectedCallResult source callee name [left, right]
      attempt fitted.expression fitted.coercions fitted.state
    change recordSelectedCallResult source callee name [left, right] attempt
      fitted.expression fitted.coercions fitted.state = result at recorded
    rw [recorded] at after
    exact (LocalGeneralizationEvents.Progress.selectFunctionCandidateFrom selected).retained.trans
      ((LocalGeneralizationEvents.Progress.withExpected fitting).retained.trans after)

theorem callArguments
    {fuel : Nat} {context : SourceInference.Context} {source callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {id : ExpressionId} {expected : Option Ty}
    {initial : State} {child : List InferredExpression × State} {result : InferredExpression × State}
    (nonconstructor : constructorCalleeCandidates context initial callee = .ok [])
    (childAccepted : inferExprsFuel fuel context arguments.elements initial = .ok child)
    (dispatch : CallExpressionDispatchProvenanceFacts context source callee arguments id expected fuel initial result) :
    BindersRetained child.2.nodes result.2.nodes := by
  cases dispatch with
  | constructor discovery _ _ => simp [nonconstructor] at discovery
  | @selected inferredArguments argumentState name candidates integerLiterals attempt _ actualArguments origin selected recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    have after := (LocalGeneralizationEvents.Progress.recordSelectedCall source callee name inferredArguments attempt).retained
    rw [recorded] at after
    exact (LocalGeneralizationEvents.Progress.selectFunctionCandidateFrom selected).retained.trans after
  | builtin _ actualArguments recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    exact (LocalGeneralizationEvents.Progress.recordBuiltinFunctionCall recorded).retained
  | @indirect inferredArguments argumentState calleeState inferredCallee application _ actualArguments _ calleeAccepted applicationAccepted recorded =>
    cases Except.ok.inj (actualArguments.symm.trans childAccepted)
    have after := (LocalGeneralizationEvents.Progress.recordIndirectCall source inferredCallee inferredArguments application).retained
    rw [recorded] at after
    exact (LocalGeneralizationEvents.inferExprFuel_origins_progress calleeAccepted).retained.trans
      ((LocalGeneralizationEvents.Progress.applyFunctionType applicationAccepted).retained.trans after)

end Solcore.SourceSemantics.SourceInferenceExecution.ActualBinderRetention
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualExpressionBinderRetention
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualBinderRetention
/-! Actual inference retains initialized binders even when it updates expression evidence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open LocalGeneralizationEvents

theorem CallIndex.bindersRetained {call : CallIndex} (accepted : call.Accepted) :
    BindersRetained call.initial.nodes call.final.nodes := by
  cases call with
  | expression => exact (inferExprFuel_origins_progress accepted).retained
  | constructorApplication => exact (inferConstructorApplicationFuel_origins_progress accepted).retained
  | constructorArguments => exact (inferConstructorArgumentsFuel_origins_progress accepted).retained
  | statements => exact (inferStatementsFuel_origins_progress accepted).retained
  | statement => exact (inferStatementFuel_origins_progress accepted).retained
  | forItems => exact (inferForItemsFuel_origins_progress accepted).retained
  | forItem => exact (inferForItemFuel_origins_progress accepted).retained
  | place => exact (inferPlaceFuel_origins_progress accepted).retained
  | assignedValue => exact (inferAssignedValueFuel_origins_progress accepted).retained
  | expressions => exact (inferExprsFuel_origins_progress accepted).retained
  | matchCases => exact (inferMatchCasesFuel_origins_progress accepted).retained

namespace ActualBinderRetention

theorem of_nodes_eq {before after : State} (same : after.nodes = before.nodes) :
    BindersRetained before.nodes after.nodes := same.symm ▸ BindersRetained.refl _

theorem unify_retained {before after : State} {left right : Ty}
    (accepted : Detail.unify before left right = .ok after) :
    BindersRetained before.nodes after.nodes :=
  of_nodes_eq (unify_occurrenceState_eq accepted).1

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualTerminalBinderRetention
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem statement_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (allocation : initial.allocateStatementId = (id, allocated))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected allocated value final).Accepted)  :
    BindersRetained (CallIndex.expression fuel context initializer expected allocated value final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases annotation
  all_goals unfold inferStatementFuel at accepted
  all_goals simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals cases Except.ok.inj accepted
  all_goals first | exact .refl _ | exact .append _ _


theorem statement_return
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .returnStmt (some value))
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).Accepted)  :
    BindersRetained (CallIndex.expression fuel context value (some expectedReturn) allocated inferred final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem statement_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {value : Syntax.Expr} {semicolon : Bool} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .expression value semicolon)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context value none allocated inferred final).Accepted)  :
    BindersRetained (CallIndex.expression fuel context value none allocated inferred final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem statement_block
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {body : List Syntax.Statement} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .block body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.statements fuel context body expectedReturn allocated bodyResult).Accepted)  :
    BindersRetained (CallIndex.statements fuel context body expectedReturn allocated bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem statement_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignValue target operator value)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).Accepted)  :
    BindersRetained (CallIndex.assignedValue fuel context target operator.value value allocated assignment inferred final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem statement_while_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted)  :
    BindersRetained (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferStatementFuel at accepted
  simp only [form, allocation, conditionAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem statement_if_else
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {body : Syntax.Block} {thenResult elseResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (hasElse : elseBody = some body)
      (thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState = .ok thenResult)
      (child : (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).Accepted)  :
    BindersRetained (CallIndex.statements fuel context body.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) elseResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  subst elseBody
  unfold inferStatementFuel at accepted
  simp only [form, allocation, conditionAccepted, thenAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  exact .append _ _


theorem forItem_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {name : Syntax.Identifier} {sourceType : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
      {expected : Option Ty} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .letDecl name sourceType (some initializer))
      (annotation : AnnotationExpected context sourceType expected)
      (child : (CallIndex.expression fuel context initializer expected initial value childFinal).Accepted)  :
    BindersRetained (CallIndex.expression fuel context initializer expected initial value childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases annotation
  all_goals unfold inferForItemFuel at accepted
  all_goals simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure]
  all_goals cases Except.ok.inj accepted
  all_goals first | exact .refl _ | exact .append _ _


theorem forItem_expression
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {value : Syntax.Expr} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .expression value)
      (child : (CallIndex.expression fuel context value none initial inferred childFinal).Accepted)  :
    BindersRetained (CallIndex.expression fuel context value none initial inferred childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferForItemFuel at accepted
  simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem forItem_assignment
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target value : Syntax.Expr} {operator : Syntax.Located Syntax.ValueAssignOp}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignValue target operator value)
      (child : (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).Accepted)  :
    BindersRetained (CallIndex.assignedValue fuel context target operator.value value initial assignment inferred childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferForItemFuel at accepted
  simp only [form, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem place_group
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {inner : Syntax.Expr} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .group inner)
      (child : (CallIndex.place fuel context inner initial value childFinal).Accepted)  :
    BindersRetained (CallIndex.place fuel context inner initial value childFinal).final.nodes (CallIndex.place (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferPlaceFuel at accepted
  simp only [form, child] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem place_index_key
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {baseValue : PlaceResolution}
      {baseState keyState valueState fitted childFinal : State} {keyType valueType : Ty}
      {keyValue : InferredExpression}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (baseAccepted : inferPlaceFuel fuel context base initial = .ok (baseValue, baseState))
      (keyFresh : baseState.fresh = (keyType, keyState))
      (valueFresh : keyState.fresh = (valueType, valueState))
      (fitting : unify valueState baseValue.type (.mapping keyType valueType) = .ok fitted)
      (child : (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).Accepted)  :
    BindersRetained (CallIndex.expression fuel context key (some (fitted.resolve keyType)) fitted keyValue childFinal).final.nodes (CallIndex.place (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferPlaceFuel at accepted
  simp only [form, baseAccepted, keyFresh, valueFresh, fitting, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem constructorArguments_tail
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      {tailValues : List InferredExpression} {tailFinal : State}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)
      (headAccepted : inferExprFuel fuel context source (some (initial.resolve expected)) initial = .ok (value, middle))
      (child : (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).Accepted)  :
    BindersRetained (CallIndex.constructorArguments fuel context sources expectedTypes middle tailValues tailFinal).final.nodes (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferConstructorArgumentsFuel at accepted
  simp only [headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem expressions_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final tailFinal : State} {value : InferredExpression}
      {values tailValues : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))
      (child : inferExprsFuel fuel context sources middle = .ok (tailValues, tailFinal))  :
    BindersRetained (CallIndex.expressions fuel context sources middle tailValues tailFinal).final.nodes (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferExprsFuel at accepted
  simp only [head, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem forItems_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial middle : State}
      {result tail : InferredForItems} {head : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)
      (headAccepted : inferForItemFuel fuel context source initial = .ok (head, middle))
      (child : (CallIndex.forItems fuel context sources middle tail).Accepted)  :
    BindersRetained (CallIndex.forItems fuel context sources middle tail).final.nodes (CallIndex.forItems fuel context (source :: sources) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferForItemsFuel at accepted
  simp only [headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _


theorem matchCases_tail
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      {tail : MatchCasesResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
      (child : (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).Accepted)  :
    BindersRetained (CallIndex.matchCases fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) tail).final.nodes (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  unfold inferMatchCasesFuel at accepted
  simp only [patternAccepted, bodyAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  cases accepted
  first | exact .refl _ | exact .append _ _

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualBranchBinderRetention
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem statement_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan}
      {place : PlaceResolution} {final : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .assignBitNot target operator)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.place fuel context target allocated place final).Accepted)  :
    BindersRetained (CallIndex.place fuel context target allocated place final).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify final place.type .word with
  | error error => simp [inferStatementFuel, allocation, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    unfold inferStatementFuel at accepted
    simp only [allocation, form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact (unify_retained fitting).trans (.append _ _)


theorem forItem_bitnot
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
      {initial final : State} {result : ForItemForm}
      {target : Syntax.Expr} {operator : Syntax.SourceSpan} {place : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.forItem (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .assignBitNot target operator)
      (child : (CallIndex.place fuel context target initial place childFinal).Accepted)  :
    BindersRetained (CallIndex.place fuel context target initial place childFinal).final.nodes (CallIndex.forItem (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify childFinal place.type .word with
  | error error => simp [inferForItemFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    unfold inferForItemFuel at accepted
    simp only [form, child, fitting, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact unify_retained fitting


theorem statement_if_then
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      {thenResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) allocated = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).Accepted)  :
    BindersRetained (CallIndex.statements fuel context thenBody.value expectedReturn conditionState thenResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases elseBody with
  | none =>
    unfold inferStatementFuel at accepted
    simp only [form, allocation, conditionAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .append _ _
  | some elseBody =>
    cases elseAccepted : inferStatementsFuel fuel context elseBody.value expectedReturn (thenResult.state.restoreLexicalScope conditionState.lexicalScope) with
    | error error => simp [inferStatementFuel, allocation, form, conditionAccepted, child, elseAccepted, bind, Except.bind] at accepted
    | ok elseResult =>
      exact (inferStatementsFuel_origins_progress elseAccepted).retained.trans
        (statement_if_else accepted form allocation conditionAccepted rfl child elseAccepted)


theorem statement_if_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {thenBody : Syntax.Block} {elseBody : Option Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .ifThen condition thenBody elseBody)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)  :
    BindersRetained (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases thenAccepted : inferStatementsFuel fuel context thenBody.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, thenAccepted, bind, Except.bind] at accepted
  | ok thenResult =>
    exact (inferStatementsFuel_origins_progress thenAccepted).retained.trans
      (statement_if_then accepted form allocation child thenAccepted)


theorem statement_while_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {condition : Syntax.Expr} {body : Syntax.Block}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .whileLoop condition body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).Accepted)  :
    BindersRetained (CallIndex.expression fuel context condition (some .bool) allocated conditionValue conditionState).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases bodyAccepted : inferStatementsFuel fuel {context with loopDepth := context.loopDepth + 1} body.value expectedReturn conditionState with
  | error error => simp [inferStatementFuel, allocation, form, child, bodyAccepted, bind, Except.bind] at accepted
  | ok bodyResult =>
    exact (inferStatementsFuel_origins_progress bodyAccepted).retained.trans
      (statement_while_body accepted form allocation child bodyAccepted)

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualForBinderRetention
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

private theorem forRetention
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initializers post : List Syntax.ForItem} {condition : Syntax.Expr} {body : Syntax.Block}
    {expected : Ty} {initial : State} {result : StatementResult}
    (receipt : SourceInference.ForStatementInferenceContinuation.Receipt fuel context source initializers condition post body expected initial result) :
    BindersRetained receipt.initialized.state.nodes result.state.nodes ∧
    BindersRetained receipt.testState.nodes result.state.nodes ∧
    BindersRetained receipt.bodyResult.state.nodes result.state.nodes ∧
    BindersRetained receipt.postResult.state.nodes result.state.nodes := by
  have tested := (inferExprFuel_origins_progress receipt.tested).retained
  have body := (inferStatementsFuel_origins_progress receipt.bodyAccepted).retained
  have post := (inferForItemsFuel_origins_progress receipt.postAccepted).retained
  have finished : BindersRetained receipt.postResult.state.nodes result.state.nodes := by
    have nodesEq := congrArg (fun r : StatementResult => r.state.nodes) receipt.completed
    rw [nodesEq]
    exact .append _ _
  have afterBody := post.trans finished
  have afterTest := body.trans afterBody
  exact ⟨tested.trans afterTest, afterTest, afterBody, finished⟩

theorem statement_for_initializer
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (child : (CallIndex.forItems fuel context initializer allocated initialized).Accepted)  :
    BindersRetained (CallIndex.forItems fuel context initializer allocated initialized).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans child)
  simpa only [sameInit] using (forRetention receipt).1



theorem statement_for_condition
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (child : (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).Accepted)  :
    BindersRetained (CallIndex.expression fuel context condition (some .bool) initialized.state conditionValue conditionState).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans initializerAccepted)
  have actualTest := receipt.tested
  rw [sameInit] at actualTest
  have sameTest := Except.ok.inj (actualTest.symm.trans child)
  have sameTestState : receipt.testState = conditionState := congrArg Prod.snd sameTest
  have sameTestValue : receipt.test = conditionValue := congrArg Prod.fst sameTest
  simpa only [sameTestState] using (forRetention receipt).2.1



theorem statement_for_body
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) initialized.state = .ok (conditionValue, conditionState))
      (child : (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).Accepted)  :
    BindersRetained (CallIndex.statements fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans initializerAccepted)
  have actualTest := receipt.tested
  rw [sameInit] at actualTest
  have sameTest := Except.ok.inj (actualTest.symm.trans conditionAccepted)
  have sameTestState : receipt.testState = conditionState := congrArg Prod.snd sameTest
  have sameTestValue : receipt.test = conditionValue := congrArg Prod.fst sameTest
  have actualBody := receipt.bodyAccepted
  rw [sameTestState] at actualBody
  have sameBody := Except.ok.inj (actualBody.symm.trans child)
  simpa only [sameBody] using (forRetention receipt).2.2.1



theorem statement_for_post
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult}
      {span : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {initialized : InferredForItems}
      {conditionValue : InferredExpression} {conditionState : State} {bodyResult : BlockResult}
      {postResult : InferredForItems}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .forLoop span initializer condition post body)
      (allocation : initial.allocateStatementId = (id, allocated))
      (initializerAccepted : inferForItemsFuel fuel context initializer allocated = .ok initialized)
      (conditionAccepted : inferExprFuel fuel context condition (some .bool) initialized.state = .ok (conditionValue, conditionState))
      (bodyAccepted : inferStatementsFuel fuel { context with loopDepth := context.loopDepth + 1 } body.value expectedReturn conditionState = .ok bodyResult)
      (child : (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).Accepted)  :
    BindersRetained (CallIndex.forItems fuel { context with loopDepth := context.loopDepth + 1 } post (bodyResult.state.restoreLexicalScope initialized.state.lexicalScope) postResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨receipt⟩ := SourceInference.ForStatementInferenceContinuation.of_accepted form accepted
  have actualInit := receipt.initialization
  rw [allocation] at actualInit
  have sameInit := Except.ok.inj (actualInit.symm.trans initializerAccepted)
  have actualTest := receipt.tested
  rw [sameInit] at actualTest
  have sameTest := Except.ok.inj (actualTest.symm.trans conditionAccepted)
  have sameTestState : receipt.testState = conditionState := congrArg Prod.snd sameTest
  have sameTestValue : receipt.test = conditionValue := congrArg Prod.fst sameTest
  have actualBody := receipt.bodyAccepted
  rw [sameTestState] at actualBody
  have sameBody := Except.ok.inj (actualBody.symm.trans bodyAccepted)
  have actualPost := receipt.postAccepted
  rw [sameInit, sameBody] at actualPost
  have samePost := Except.ok.inj (actualPost.symm.trans child)
  simpa only [samePost] using (forRetention receipt).2.2.2


end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualListBinderRetention
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem expressions_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Expr} {sources : List Syntax.Expr}
      {initial middle final : State} {value : InferredExpression}
      {values : List InferredExpression}
      (accepted : (CallIndex.expressions (fuel + 1) context (source :: sources)
        initial values final).Accepted)
      (head : inferExprFuel fuel context source none initial = .ok (value, middle))  :
    BindersRetained (CallIndex.expression fuel context source none initial value middle).final.nodes (CallIndex.expressions (fuel + 1) context (source :: sources) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferExprsFuel fuel context sources middle with
  | error error => simp [inferExprsFuel, head, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferExprsFuel_origins_progress tailAccepted).retained.trans
      (expressions_tail accepted head tailAccepted)


theorem constructorArguments_head
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {sources : List Syntax.Expr}
      {expected : Ty} {expectedTypes : List Ty} {initial middle final : State}
      {values : List InferredExpression} {value : InferredExpression}
      (accepted : (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).Accepted)

      (child : (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).Accepted)  :
    BindersRetained (CallIndex.expression fuel context source (some (initial.resolve expected)) initial value middle).final.nodes (CallIndex.constructorArguments fuel context (source :: sources) (expected :: expectedTypes) initial values final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferConstructorArgumentsFuel fuel context sources expectedTypes middle with
  | error error => simp [inferConstructorArgumentsFuel, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferConstructorArgumentsFuel_origins_progress tailAccepted).retained.trans
      (constructorArguments_tail accepted child tailAccepted)


theorem forItems_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.ForItem} {sources : List Syntax.ForItem} {initial final : State}
      {result : InferredForItems} {value : ForItemForm}
      (accepted : (CallIndex.forItems fuel context (source :: sources) initial result).Accepted)

      (child : (CallIndex.forItem fuel context source initial value final).Accepted)  :
    BindersRetained (CallIndex.forItem fuel context source initial value final).final.nodes (CallIndex.forItems fuel context (source :: sources) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferForItemsFuel fuel context sources final with
  | error error => simp [inferForItemsFuel, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferForItemsFuel_origins_progress tailAccepted).retained.trans
      (forItems_tail accepted child tailAccepted)


theorem statements_tail
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result tail : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)
      (nonempty : sources ≠ [])
      (headAccepted : inferStatementFuel fuel context source expectedReturn initial = .ok head)
      (child : (CallIndex.statements fuel context sources expectedReturn head.state tail).Accepted)  :
    BindersRetained (CallIndex.statements fuel context sources expectedReturn head.state tail).final.nodes (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases sources with
  | nil => exact False.elim (nonempty rfl)
  | cons next rest =>
    simp only [inferStatementsFuel, headAccepted, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .refl _


theorem statements_head
      {fuel : Nat} {context : SourceInference.Context}
      {source : Syntax.Statement} {sources : List Syntax.Statement} {expectedReturn : Ty}
      {initial : State} {result : BlockResult} {head : StatementResult}
      (accepted : (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).Accepted)

      (child : (CallIndex.statement fuel context source expectedReturn initial head).Accepted)  :
    BindersRetained (CallIndex.statement fuel context source expectedReturn initial head).final.nodes (CallIndex.statements (fuel + 1) context (source :: sources) expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases sources with
  | nil =>
    simp only [inferStatementsFuel, child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact .refl _
  | cons next rest =>
    cases tailAccepted : inferStatementsFuel fuel context (next :: rest) expectedReturn head.state with
    | error error => simp [inferStatementsFuel, child, tailAccepted, bind, Except.bind] at accepted
    | ok tail =>
      have nonempty : next :: rest ≠ [] := List.cons_ne_nil _ _
      exact (inferStatementsFuel_origins_progress tailAccepted).retained.trans
        (statements_tail accepted nonempty child tailAccepted)

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMatchBinderRetention
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem statement_match_default
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
      {checked : MatchCasesResult}
      {body : Syntax.Block} {bodyResult : BlockResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
      (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
      (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState = .ok checked)
      (default : arms.value.defaultBody = some body)
      (child : (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).Accepted)  :
    BindersRetained (CallIndex.statements fuel context body.value expectedReturn checked.state bodyResult).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  unfold matchCompletion at completion
  simp only [casesAccepted, default, child, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
  split at completion
  · contradiction
  · cases Except.ok.inj completion
    exact .append _ _


theorem statement_match_cases
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : InferredExpression} {scrutineeState hiddenState : State} {hidden : Resolved.LocalId}
      {checked : MatchCasesResult}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState))
      (hiddenAllocation : scrutineeState.allocateHiddenLocal = (hidden, hiddenState))
      (child : (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).Accepted)  :
    BindersRetained (CallIndex.matchCases fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState checked).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
  cases defaultEq : arms.value.defaultBody with
  | none =>
    unfold matchCompletion at completion
    simp only [child, defaultEq, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
    split at completion
    · contradiction
    · cases Except.ok.inj completion
      exact .append _ _
  | some body =>
    cases bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state with
    | error error => simp [matchCompletion, child, defaultEq, bodyAccepted, bind, Except.bind] at completion
    | ok bodyResult =>
      exact (inferStatementsFuel_origins_progress bodyAccepted).retained.trans
        (statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation child defaultEq bodyAccepted)

private theorem afterScrutinee
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (accepted : inferStatementFuel (fuel+1) context source expectedReturn initial = .ok result)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState)) :
    BindersRetained scrutineeState.nodes result.state.nodes := by
  let hidden := scrutineeState.allocateHiddenLocal.1
  let hiddenState := scrutineeState.allocateHiddenLocal.2
  have completion := matchCompletion_accepted form allocation scrutineeAccepted (show scrutineeState.allocateHiddenLocal = (hidden, hiddenState) from rfl) accepted
  cases casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn hiddenState.lexicalScope arms.value.cases hiddenState with
  | error error => simp [matchCompletion, casesAccepted, bind, Except.bind] at completion
  | ok checked =>
    exact (inferMatchCasesFuel_origins_progress casesAccepted).retained.trans
      (statement_match_cases accepted form allocation scrutineeAccepted rfl casesAccepted)

theorem statement_match_single
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {scrutinee : Syntax.Expr} {value : InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (single : scrutinees.elements.toList = [scrutinee])
      (child : (CallIndex.expression fuel context scrutinee none allocated value childFinal).Accepted)  :
    BindersRetained (CallIndex.expression fuel context scrutinee none allocated value childFinal).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (value, childFinal) := by simpa only [matchScrutinee, single] using child
  exact afterScrutinee accepted form allocation scrutineeAccepted


theorem statement_match_many
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
      {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
      {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
      {arms : Syntax.MatchArms}
      {values : List InferredExpression} {childFinal : State}
      (accepted : (CallIndex.statement (fuel + 1) context source expectedReturn initial result).Accepted)
      (form : source.value = .matchWith scrutinees arms)
      (allocation : initial.allocateStatementId = (id, allocated))
      (multiple : ∀ scrutinee, scrutinees.elements.toList ≠ [scrutinee])
      (child : (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).Accepted)  :
    BindersRetained (CallIndex.expressions fuel context scrutinees.elements.toList allocated values childFinal).final.nodes (CallIndex.statement (fuel + 1) context source expectedReturn initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  let tuple : InferredExpression := ⟨childFinal.allocateExpressionId.1, Ty.productMany (values.map (·.type))⟩
  let tupleState := childFinal.allocateExpressionId.2.recordNode (.expression {
    id := tuple.id, span := source.span, type := tuple.type, form := .tuple (values.map (·.id)) })
  have scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (tuple, tupleState) := by
    unfold matchScrutinee
    split
    · rename_i sourceEq
      exact False.elim (multiple _ sourceEq)
    · simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure]
      rfl
  exact (BindersRetained.append _ _).trans (afterScrutinee accepted form allocation scrutineeAccepted)

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualMutableBinderRetention
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail LocalGeneralizationEvents
namespace ActualBinderRetention

theorem assignedValue_value
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      {fitted childFinal : State} {childValue : InferredExpression}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)
      (targetAccepted : inferPlaceFuel fuel context target initial = .ok (place, targetState))
      (fitting : (match operator with | .equal => pure targetState | _ => unify targetState place.type .word) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).Accepted)  :
    BindersRetained (CallIndex.expression fuel context value (some (assignmentExpected operator fitted place.type)) fitted childValue childFinal).final.nodes (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨actualPlace, actualState, actualFitted, actualPlaceAccepted, actualFitting, actualValueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans targetAccepted)
  have actualFitting : assignmentFit operator targetState place.type = (Except.ok actualFitted : Except Error State) := by cases operator <;> exact actualFitting
  have fitting : assignmentFit operator targetState place.type = (Except.ok fitted : Except Error State) := by cases operator <;> exact fitting
  cases Except.ok.inj (actualFitting.symm.trans fitting)
  cases Except.ok.inj (actualValueAccepted.symm.trans child)
  exact .refl _


theorem assignedValue_place
      {fuel : Nat} {context : SourceInference.Context} {target value : Syntax.Expr}
      {operator : Syntax.ValueAssignOp} {initial final targetState : State}
      {assignment : AssignmentResolution} {inferred : InferredExpression} {place : PlaceResolution}
      (accepted : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Accepted)

      (child : (CallIndex.place fuel context target initial place targetState).Accepted)  :
    BindersRetained (CallIndex.place fuel context target initial place targetState).final.nodes (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  obtain ⟨actualPlace, actualState, fitted, actualPlaceAccepted, fitting, valueAccepted, _⟩ := assignedValue_actual_prefix accepted
  cases Except.ok.inj (actualPlaceAccepted.symm.trans child)
  have fitRetained : BindersRetained targetState.nodes fitted.nodes := by
    cases operator <;> simp only [pure, Pure.pure, Except.pure] at fitting
    all_goals first
    | (cases Except.ok.inj fitting; exact .refl _)
    | exact unify_retained fitting
  exact fitRetained.trans (inferExprFuel_origins_progress valueAccepted).retained


theorem place_index_base
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr}
      {initial final : State} {result : PlaceResolution}
      {base key : Syntax.Expr} {brackets : Syntax.SourceSpan} {value : PlaceResolution} {childFinal : State}
      (accepted : (CallIndex.place (fuel + 1) context source initial result final).Accepted)
      (form : source.value = .index base brackets key)
      (child : (CallIndex.place fuel context base initial value childFinal).Accepted)  :
    BindersRetained (CallIndex.place fuel context base initial value childFinal).final.nodes (CallIndex.place (fuel + 1) context source initial result final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases fitting : Detail.unify childFinal.fresh.2.fresh.2 value.type (.mapping childFinal.fresh.1 childFinal.fresh.2.fresh.1) with
  | error error => simp [inferPlaceFuel, form, child, fitting, bind, Except.bind] at accepted
  | ok fitted =>
    cases keyAccepted : inferExprFuel fuel context key (some (fitted.resolve childFinal.fresh.1)) fitted with
    | error error => simp [inferPlaceFuel, form, child, fitting, keyAccepted, bind, Except.bind] at accepted
    | ok keyResult =>
      exact (unify_retained fitting).trans ((inferExprFuel_origins_progress keyAccepted).retained.trans
        (place_index_key accepted form child rfl rfl fitting keyAccepted))


theorem constructorApplication_arguments
      {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Expr} {id : ExpressionId}
      {instantiation : DataConstructorInstantiation} {sources : List Syntax.Expr} {expected : Option Ty}
      {initial fitted final childFinal : State} {value : InferredExpression} {values : List InferredExpression}
      (accepted : (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).Accepted)
      (arity : sources.length = instantiation.payloadTypes.length)
      (fitting : (match expected with | none => pure initial | some type => unify initial instantiation.resultType type) = (Except.ok fitted : Except Error State))
      (child : (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).Accepted)  :
    BindersRetained (CallIndex.constructorArguments fuel context sources instantiation.payloadTypes fitted values childFinal).final.nodes (CallIndex.constructorApplication fuel context source id instantiation sources expected initial value final).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  have fitting : (match expected with | none => Except.ok initial | some type => Detail.unify initial instantiation.resultType type) = .ok fitted := by cases expected <;> exact fitting
  have recorded : recordExpressionWithExpected context source id (childFinal.resolve instantiation.resultType)
      (.constructor instantiation (values.map (·.id))) [] expected childFinal = .ok (value, final) := by
    unfold inferConstructorApplicationFuel at accepted
    cases expected with
    | none => cases Except.ok.inj fitting; simpa [arity, child, bind, Except.bind, pure, Pure.pure, Except.pure] using accepted
    | some type => simpa [arity, fitting, child, bind, Except.bind] using accepted
  exact BindersRetained.recordExpressionWithExpected recorded


theorem matchCases_body
      {fuel : Nat} {context : SourceInference.Context} {scrutineeType expectedReturn : Ty}
      {saved : LexicalScope} {arm : Syntax.MatchCase} {arms : List Syntax.MatchCase}
      {initial patternState : State} {pattern : TypedMatchPattern} {result : MatchCasesResult}
      {body : BlockResult}
      (accepted : (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).Accepted)
      (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutineeType initial = .ok (pattern, patternState))
      (child : (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).Accepted)  :
    BindersRetained (CallIndex.statements fuel context arm.value.body.value expectedReturn patternState body).final.nodes (CallIndex.matchCases (fuel + 1) context scrutineeType expectedReturn saved (arm :: arms) initial result).final.nodes := by
  simp only [CallIndex.Accepted] at accepted child
  dsimp only [CallIndex.final] at ⊢
  cases tailAccepted : inferMatchCasesFuel fuel context scrutineeType expectedReturn saved arms (body.state.restoreLexicalScope saved) with
  | error error => simp [inferMatchCasesFuel, patternAccepted, child, tailAccepted, bind, Except.bind] at accepted
  | ok tail =>
    exact (inferMatchCasesFuel_origins_progress tailAccepted).retained.trans
      (matchCases_tail accepted patternAccepted child tailAccepted)

end ActualBinderRetention
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualNonExpressionBinderRetention
/-! Every non-expression child preserves all initialized binders through its actual suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution

theorem ChildStep.nonexpression_binders_retained {parent child : CallIndex}
    (step : ChildStep parent child)
    (nonexpression : parent.NonExpression) :
    Frontend.SourceInference.LocalGeneralizationEvents.BindersRetained child.final.nodes parent.final.nodes := by
  cases step with
  | expression_group accepted form allocation child =>
      exact False.elim nonexpression
  | expression_tuple accepted form allocation child =>
      exact False.elim nonexpression
  | expressions_head accepted head =>
      exact ActualBinderRetention.expressions_head accepted head
  | expressions_tail accepted head tail =>
      exact ActualBinderRetention.expressions_tail accepted head tail
  | statements_head accepted child =>
      exact ActualBinderRetention.statements_head accepted child
  | statements_tail accepted nonempty headAccepted child =>
      exact ActualBinderRetention.statements_tail accepted nonempty headAccepted child
  | statement_initializer accepted form allocation annotation child =>
      exact ActualBinderRetention.statement_initializer accepted form allocation annotation child
  | statement_return accepted form allocation child =>
      exact ActualBinderRetention.statement_return accepted form allocation child
  | statement_expression accepted form allocation child =>
      exact ActualBinderRetention.statement_expression accepted form allocation child
  | statement_block accepted form allocation child =>
      exact ActualBinderRetention.statement_block accepted form allocation child
  | statement_if_condition accepted form allocation child =>
      exact ActualBinderRetention.statement_if_condition accepted form allocation child
  | statement_if_then accepted form allocation conditionAccepted child =>
      exact ActualBinderRetention.statement_if_then accepted form allocation conditionAccepted child
  | statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child =>
      exact ActualBinderRetention.statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child
  | statement_assignment accepted form allocation child =>
      exact ActualBinderRetention.statement_assignment accepted form allocation child
  | statement_bitnot accepted form allocation child =>
      exact ActualBinderRetention.statement_bitnot accepted form allocation child
  | statement_while_condition accepted form allocation child =>
      exact ActualBinderRetention.statement_while_condition accepted form allocation child
  | statement_while_body accepted form allocation conditionAccepted child =>
      exact ActualBinderRetention.statement_while_body accepted form allocation conditionAccepted child
  | statement_for_initializer accepted form allocation child =>
      exact ActualBinderRetention.statement_for_initializer accepted form allocation child
  | statement_for_condition accepted form allocation initializerAccepted child =>
      exact ActualBinderRetention.statement_for_condition accepted form allocation initializerAccepted child
  | statement_for_body accepted form allocation initializerAccepted conditionAccepted child =>
      exact ActualBinderRetention.statement_for_body accepted form allocation initializerAccepted conditionAccepted child
  | statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
      exact ActualBinderRetention.statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child
  | forItems_head accepted child =>
      exact ActualBinderRetention.forItems_head accepted child
  | forItems_tail accepted headAccepted child =>
      exact ActualBinderRetention.forItems_tail accepted headAccepted child
  | forItem_initializer accepted form annotation child =>
      exact ActualBinderRetention.forItem_initializer accepted form annotation child
  | forItem_expression accepted form child =>
      exact ActualBinderRetention.forItem_expression accepted form child
  | forItem_assignment accepted form child =>
      exact ActualBinderRetention.forItem_assignment accepted form child
  | forItem_bitnot accepted form child =>
      exact ActualBinderRetention.forItem_bitnot accepted form child
  | assignedValue_place accepted child =>
      exact ActualBinderRetention.assignedValue_place accepted child
  | assignedValue_value accepted targetAccepted fitting child =>
      exact ActualBinderRetention.assignedValue_value accepted targetAccepted fitting child
  | place_group accepted form child =>
      exact ActualBinderRetention.place_group accepted form child
  | place_index_base accepted form child =>
      exact ActualBinderRetention.place_index_base accepted form child
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting child =>
      exact ActualBinderRetention.place_index_key accepted form baseAccepted keyFresh valueFresh fitting child
  | constructorApplication_arguments accepted arity fitting child =>
      exact ActualBinderRetention.constructorApplication_arguments accepted arity fitting child
  | constructorArguments_head accepted child =>
      exact ActualBinderRetention.constructorArguments_head accepted child
  | constructorArguments_tail accepted headAccepted child =>
      exact ActualBinderRetention.constructorArguments_tail accepted headAccepted child
  | expression_unary accepted form allocation child =>
      exact False.elim nonexpression
  | expression_binary_left accepted form allocation child =>
      exact False.elim nonexpression
  | expression_binary_right accepted form allocation leftAccepted child =>
      exact False.elim nonexpression
  | expression_conditional_condition accepted form allocation child =>
      exact False.elim nonexpression
  | expression_conditional_then accepted form allocation conditionAccepted child =>
      exact False.elim nonexpression
  | expression_conditional_else accepted form allocation conditionAccepted thenAccepted child =>
      exact False.elim nonexpression
  | expression_lambda_body accepted form allocation parametersAccepted prefixFacts child =>
      exact False.elim nonexpression
  | expression_index_base accepted form allocation child =>
      exact False.elim nonexpression
  | expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
      exact False.elim nonexpression
  | expression_call_constructor accepted form allocation selected fresh child =>
      exact False.elim nonexpression
  | expression_call_arguments accepted form allocation nonconstructor child =>
      exact False.elim nonexpression
  | expression_call_callee accepted form allocation nonconstructor argumentsAccepted indirect child =>
      exact False.elim nonexpression
  | expression_contextual_constructor accepted form allocation selected child =>
      exact False.elim nonexpression
  | expression_field_constructor accepted form allocation selected fresh child =>
      exact False.elim nonexpression
  | matchCases_body accepted patternAccepted child =>
      exact ActualBinderRetention.matchCases_body accepted patternAccepted child
  | matchCases_tail accepted patternAccepted bodyAccepted child =>
      exact ActualBinderRetention.matchCases_tail accepted patternAccepted bodyAccepted child
  | statement_match_single accepted form allocation single child =>
      exact ActualBinderRetention.statement_match_single accepted form allocation single child
  | statement_match_many accepted form allocation multiple child =>
      exact ActualBinderRetention.statement_match_many accepted form allocation multiple child
  | statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child =>
      exact ActualBinderRetention.statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child
  | statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
      exact ActualBinderRetention.statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualBinderContinuation
/-! An actual child keeps both declarations recorded in its node table and
header declarations awaiting their enclosing loop statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference
open LocalGeneralizationEvents (BindersRetained)

private theorem item_binders (item : ForItemForm) :
    item.initializedLetBinders = (forItemInitializedLetBindings item).map (·.binder) := by
  cases item <;> try rfl
  rename_i binder initializer
  cases initializer <;> rfl

private theorem statement_binders (form : StatementForm) :
    form.initializedLetBinders = (statementInitializedLetBindings form).map (·.binder) := by
  cases form <;> try rfl
  · rename_i binder initializer
    cases initializer <;> rfl
  · simp only [StatementForm.initializedLetBinders, statementInitializedLetBindings,
      List.map_append, List.map_flatMap]
    simp only [← item_binders]

private theorem source_binders (source : TypedSource) :
    source.initializedLetBinders = (initializedLetBindings source).map (·.binder) := by
  simp only [TypedSource.initializedLetBinders, initializedLetBindings, List.map_flatMap]
  apply congrArg (fun f : Node → List TypedBinder => source.nodes.flatMap f)
  funext node
  cases node with
  | expression node => rfl
  | statement node => exact statement_binders node.form

def CallIndex.initializedBinders (call : CallIndex) : List TypedBinder :=
  call.final.nodes.flatMap Node.initializedLetBinders ++ call.returnedBindings.map (·.binder)

theorem ChildStep.binders_retained {parent child : CallIndex}
    (step : ChildStep parent child) :
    BindersRetained child.final.nodes parent.final.nodes := by
  cases parent <;> first
  | exact step.expression_binders_retained
  | exact step.nonexpression_binders_retained (by trivial)

theorem ChildStep.initialized_binders {parent child : CallIndex}
    (step : ChildStep parent child) :
    child.initializedBinders ⊆ parent.initializedBinders := by
  intro binder present
  rcases List.mem_append.mp present with recorded | pending
  · exact List.mem_append_left _ (step.binders_retained recorded)
  · obtain ⟨binding, member, same⟩ := List.mem_map.mp pending
    rcases List.mem_append.mp (step.returned_bindings member) with recorded | pending
    · apply List.mem_append_left
      change binder ∈ (parent.final.toTypedSource []).initializedLetBinders
      rw [source_binders]
      exact List.mem_map.mpr ⟨binding, recorded, same⟩
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨binding, pending, same⟩)

theorem CallOccurrence.initialized_binders {root call : CallIndex}
    (here : CallOccurrence root call) :
    call.initializedBinders ⊆ root.initializedBinders := by
  induction here with
  | root accepted => exact fun _ present => present
  | child prior step ih => exact fun _ present => ih (step.initialized_binders present)

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCaptureResults
/-! Actual statement and header results expose every new polymorphic binder. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceInferenceSoundness.ProtectedVariables
namespace ActualCaptureOrigins

theorem statement_result
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult} {whole : TypedSource}
    (accepted : inferStatementFuel fuel context source expected initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : (result.state.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders) :
    ActiveBinderCaptureOrigins result.state whole := by
  constructor
  intro binder member
  rcases inferStatementFuel_quantified_origin accepted binder member with old | mono | created
  · exact origins.origin binder old
  · exact .inl mono
  · obtain ⟨childFuel, receipt, rfl⟩ := created
    apply Or.inr
    apply retained
    exact List.mem_flatMap.mpr ⟨_, receipt.recorded, by
      simp [Node.initializedLetBinders, StatementForm.initializedLetBinders]⟩

theorem header_result
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State} {whole : TypedSource}
    (accepted : inferForItemFuel fuel context source initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : ∀ binding ∈ forItemInitializedLetBindings result.1,
      binding.binder ∈ whole.initializedLetBinders) :
    ActiveBinderCaptureOrigins result.2 whole := by
  constructor
  intro binder member
  rcases inferForItemFuel_quantified_origin accepted binder member with old | mono | created
  · exact origins.origin binder old
  · exact .inl mono
  · obtain ⟨childFuel, receipt, rfl⟩ := created
    apply Or.inr
    apply retained ⟨receipt.binding.1, .expression receipt.value.id⟩
    simp only [receipt.recorded, forItemInitializedLetBindings, List.mem_singleton]

theorem headers_result
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.ForItem}
    {initial : State} {result : InferredForItems} {whole : TypedSource}
    (accepted : inferForItemsFuel fuel context sources initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : ∀ binding ∈ result.items.flatMap forItemInitializedLetBindings,
      binding.binder ∈ whole.initializedLetBinders) :
    ActiveBinderCaptureOrigins result.state whole := by
  induction sources generalizing initial result with
  | nil =>
    simp only [inferForItemsFuel, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact origins
  | cons source sources ih =>
    cases headAccepted : inferForItemFuel fuel context source initial with
    | error error => simp [inferForItemsFuel, headAccepted, bind, Except.bind] at accepted
    | ok head =>
      cases tailAccepted : inferForItemsFuel fuel context sources head.2 with
      | error error => simp [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind] at accepted
      | ok tail =>
        simp only [inferForItemsFuel, headAccepted, tailAccepted, bind, Except.bind, pure,
          Pure.pure, Except.pure, Except.ok.injEq] at accepted
        cases accepted
        have headOrigins := header_result headAccepted origins (fun binding member =>
          retained binding (List.mem_append_left _ member))
        exact ih (result := tail) tailAccepted headOrigins (fun binding member =>
          retained binding (List.mem_append_right _ member))

theorem statements_result
    {fuel : Nat} {context : SourceInference.Context} {sources : List Syntax.Statement}
    {expected : Ty} {initial : State} {result : BlockResult} {whole : TypedSource}
    (accepted : inferStatementsFuel fuel context sources expected initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole)
    (retained : (result.state.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders) :
    ActiveBinderCaptureOrigins result.state whole := by
  induction fuel generalizing sources initial result with
  | zero => simp [inferStatementsFuel] at accepted
  | succ fuel ih =>
    cases sources with
    | nil =>
      simp only [inferStatementsFuel, Except.ok.injEq] at accepted
      cases accepted
      exact origins
    | cons source sources =>
      cases sources with
      | nil =>
        obtain ⟨head, headAccepted, same⟩ := inferStatementsFuel_success_singleton_facts accepted
        have headOrigins := statement_result headAccepted origins (by simpa only [same] using retained)
        simpa only [same] using headOrigins
      | cons next rest =>
        obtain ⟨head, tail, headAccepted, tailAccepted, same⟩ := inferStatementsFuel_success_cons_facts accepted
        have tailRetained : (tail.state.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders :=
          by simpa only [same] using retained
        have headRetained : (head.state.toTypedSource []).initializedLetBinders ⊆ whole.initializedLetBinders :=
          fun _ member => tailRetained ((LocalGeneralizationEvents.inferStatementsFuel_origins_progress tailAccepted).retained member)
        have headOrigins := statement_result headAccepted origins headRetained
        have tailOrigins := ih tailAccepted headOrigins tailRetained
        simpa only [same] using tailOrigins

end ActualCaptureOrigins
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCaptureScopes
/-! Real monomorphic parameter and pattern allocations preserve capture origins. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceInferenceSoundness.ProtectedVariables
namespace ActualCaptureOrigins

theorem of_scope {initial final : State} {whole : TypedSource}
    (origins : ActiveBinderCaptureOrigins initial whole)
    (same : final.lexicalScope = initial.lexicalScope) :
    ActiveBinderCaptureOrigins final whole :=
  origins.congr_localBinders (congrArg LexicalScope.binders same)

theorem freshConstructor {initial final : State} {whole : TypedSource}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (origins : ActiveBinderCaptureOrigins initial whole)
    (accepted : freshDataConstructorInstantiation dataType constructor initial = (instantiation, final)) :
    ActiveBinderCaptureOrigins final whole := by
  have same := freshDataConstructorInstantiation_preserves_lexicalScope dataType constructor initial
  rw [accepted] at same
  exact of_scope origins same

theorem lambdaParameters
    {context : SourceInference.Context} {parameters : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {initial : State}
    {result : List TypedBinder × List Ty × State} {whole : TypedSource}
    (accepted : bindLambdaParameters context parameters index seen initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole) :
    ActiveBinderCaptureOrigins result.2.2 whole := by
  induction parameters generalizing index seen initial result with
  | nil =>
    simp only [bindLambdaParameters] at accepted
    cases Except.ok.inj accepted
    exact origins
  | cons parameter rest ih =>
    cases form : parameter.value with
    | error => simp [bindLambdaParameters, form, bind, Except.bind] at accepted
    | inferred name =>
      simp only [bindLambdaParameters, form, bind, Except.bind] at accepted
      repeat' first | split at accepted
      all_goals try simp_all only [exceptPure_eq_ok]
      all_goals try simp_all
      all_goals
        subst result
        subst_vars
        have freshOrigins : ActiveBinderCaptureOrigins initial.fresh.2 whole :=
          origins.congr_localBinders rfl
        have allocatedOrigins : ActiveBinderCaptureOrigins
            (initial.fresh.2.allocateBinder name.value (.mono initial.fresh.1)
              (some parameter.span) false []).2 whole :=
          freshOrigins.allocateBinder rfl (.inl rfl)
        exact ih _ _ _ (by assumption) allocatedOrigins
    | typed marker name sourceType =>
      simp only [bindLambdaParameters, form] at accepted
      cases resolved : resolveSourceType context sourceType with
      | error error => simp [resolved, bind, Except.bind] at accepted
      | ok type =>
        simp only [resolved, bind, Except.bind] at accepted
        repeat' first | split at accepted
        all_goals try simp_all only [exceptPure_eq_ok]
        all_goals try simp_all
        all_goals
          subst result
          subst_vars
          exact ih _ _ _ (by assumption) (origins.allocateBinder rfl (.inl rfl))

theorem lambdaPrefix
    {context : SourceInference.Context} {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {types : List Ty} {initial final : State} {resultType : Ty} {whole : TypedSource}
    (facts : LambdaPrefixFacts context expected annotation types initial resultType final)
    (origins : ActiveBinderCaptureOrigins initial whole) :
    ActiveBinderCaptureOrigins final whole := by
  cases facts with
  | noExpectedPartsAnnotated => exact origins
  | noExpectedPartsFresh _ _ fresh =>
    have same : initial.fresh.2 = final := congrArg Prod.snd fresh
    rw [← same]
    exact origins.congr_localBinders rfl
  | expectedPartsAnnotated _ unified => exact origins.unify unified
  | expectedPartsInferred _ unified => exact origins.unify unified

theorem pattern
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial : State} {result : TypedMatchPattern × State} {whole : TypedSource}
    (accepted : inferMatchPatternFuel fuel context pattern expected initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole) :
    ActiveBinderCaptureOrigins result.2 whole :=
  (inferMatchPatternFuel_scope accepted).captureOrigins origins

theorem scrutinee
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {result : InferredExpression × State}
    {whole : TypedSource}
    (accepted : matchScrutinee fuel context span sources initial = .ok result)
    (origins : ActiveBinderCaptureOrigins initial whole) :
    ActiveBinderCaptureOrigins result.2 whole := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact origins.inferExprFuel accepted
  · cases children : inferExprsFuel fuel context sources initial with
    | error error => simp [children, bind, Except.bind] at accepted
    | ok values =>
      simp only [children, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
      cases Except.ok.inj accepted
      exact (origins.inferExprsFuel children).congr_localBinders rfl

end ActualCaptureOrigins
end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualCaptureEntries
/-! Capture origins follow each actual child entry, using retained declarations
only for earlier statement and header calls in the same execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceInferenceSoundness.ProtectedVariables ActualCaptureOrigins

theorem ChildStep.captureOrigins
    {parent destination : CallIndex} {whole : TypedSource}
    (step : ChildStep parent destination) (inputs : parent.Inputs)
    (origins : ActiveBinderCaptureOrigins parent.initial whole)
    (retained : ∀ {prior : CallIndex}, ChildStep parent prior → prior.CaptureRetained whole) :
    ActiveBinderCaptureOrigins destination.initial whole := by
  cases step with
  | @expression_group fuel context source inner expected initial allocated final childFinal id value childValue accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_tuple fuel context source elements expected initial allocated final childFinal id value values accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expressions_head fuel context source sources initial middle final value values accepted head =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @expressions_tail fuel context source sources initial middle final tailFinal value values tailValues accepted head tail =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.inferExprFuel head
  | @statements_head fuel context source sources expectedReturn initial result head accepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @statements_tail fuel context source sources expectedReturn initial result tail head accepted nonempty headAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.statements_head accepted headAccepted)
    exact statement_result headAccepted origins kept.nodes
  | @statement_initializer fuel context source expectedReturn initial allocated id result name sourceType initializer expected value final accepted form allocation annotation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_return fuel context source expectedReturn initial allocated id result value inferred final accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_expression fuel context source expectedReturn initial allocated id result value semicolon inferred final accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_block fuel context source expectedReturn initial allocated id result body bodyResult accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_if_condition fuel context source expectedReturn initial allocated id result condition thenBody elseBody conditionValue conditionState accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_if_then fuel context source expectedReturn initial allocated id result condition thenBody elseBody conditionValue conditionState thenResult accepted form allocation conditionAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateStatementId allocation).inferExprFuel conditionAccepted
  | @statement_if_else fuel context source expectedReturn initial allocated id result condition thenBody elseBody conditionValue conditionState body thenResult elseResult accepted form allocation conditionAccepted hasElse thenAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact ((origins.allocateStatementId allocation).inferExprFuel conditionAccepted).restoreLexicalScope
  | @statement_assignment fuel context source expectedReturn initial allocated id result target value operator assignment inferred final accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_bitnot fuel context source expectedReturn initial allocated id result target operator place final accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_while_condition fuel context source expectedReturn initial allocated id result condition body conditionValue conditionState accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_while_body fuel context source expectedReturn initial allocated id result condition body conditionValue conditionState bodyResult accepted form allocation conditionAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateStatementId allocation).inferExprFuel conditionAccepted
  | @statement_for_initializer fuel context source expectedReturn initial allocated id result span initializer post condition body initialized accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_for_condition fuel context source expectedReturn initial allocated id result span initializer post condition body initialized conditionValue conditionState accepted form allocation initializerAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.statement_for_initializer accepted form allocation initializerAccepted)
    exact headers_result initializerAccepted (origins.allocateStatementId allocation) kept.returned
  | @statement_for_body fuel context source expectedReturn initial allocated id result span initializer post condition body initialized conditionValue conditionState bodyResult accepted form allocation initializerAccepted conditionAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.statement_for_initializer accepted form allocation initializerAccepted)
    exact (headers_result initializerAccepted (origins.allocateStatementId allocation) kept.returned).inferExprFuel conditionAccepted
  | @statement_for_post fuel context source expectedReturn initial allocated id result span initializer post condition body initialized conditionValue conditionState bodyResult postResult accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.statement_for_initializer accepted form allocation initializerAccepted)
    exact (headers_result initializerAccepted (origins.allocateStatementId allocation) kept.returned).restoreLexicalScope
  | @forItems_head fuel context source sources initial final result value accepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @forItems_tail fuel context source sources initial middle result tail head accepted headAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have kept := retained (ChildStep.forItems_head accepted headAccepted)
    exact header_result headAccepted origins kept.returned
  | @forItem_initializer fuel context source initial final result name sourceType initializer expected value childFinal accepted form annotation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @forItem_expression fuel context source initial final result value inferred childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @forItem_assignment fuel context source initial final result target value operator assignment inferred childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @forItem_bitnot fuel context source initial final result target operator place childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @assignedValue_place fuel context target value operator initial final targetState assignment inferred place accepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @assignedValue_value fuel context target value operator initial final targetState assignment inferred place fitted childFinal childValue accepted targetAccepted fitting child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have targetOrigins := origins.inferPlaceFuel targetAccepted
    cases operator <;> simp only [pure, Pure.pure, Except.pure] at fitting
    all_goals first
    | (cases Except.ok.inj fitting; exact targetOrigins)
    | exact targetOrigins.unify fitting
  | @place_group fuel context source initial final result inner value childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @place_index_base fuel context source initial final result base key brackets value childFinal accepted form child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @place_index_key fuel context source initial final result base key brackets baseValue baseState keyState valueState fitted childFinal keyType valueType keyValue accepted form baseAccepted keyFresh valueFresh fitting child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have baseOrigins := origins.inferPlaceFuel baseAccepted
    have keyOrigins : ActiveBinderCaptureOrigins keyState whole := by
      have same : keyState = baseState.fresh.2 := (congrArg Prod.snd keyFresh).symm
      rw [same]
      exact baseOrigins.congr_localBinders rfl
    have valueOrigins : ActiveBinderCaptureOrigins valueState whole := by
      have same : valueState = keyState.fresh.2 := (congrArg Prod.snd valueFresh).symm
      rw [same]
      exact keyOrigins.congr_localBinders rfl
    exact valueOrigins.unify fitting
  | @constructorApplication_arguments fuel context source id instantiation sources expected initial fitted final childFinal value values accepted arity fitting child =>
    dsimp only [CallIndex.initial] at origins ⊢
    cases expected with
    | none => cases Except.ok.inj fitting; exact origins
    | some expected => exact origins.unify fitting
  | @constructorArguments_head fuel context source sources expected expectedTypes initial middle final values value accepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins
  | @constructorArguments_tail fuel context source sources expected expectedTypes initial middle final values value tailValues tailFinal accepted headAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.inferExprFuel headAccepted
  | @expression_unary fuel context source expected initial allocated final id value operator operand inferred childFinal accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_binary_left fuel context source expected initial allocated final id value operator left right leftValue leftState accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_binary_right fuel context source expected initial allocated final id value operator left right leftValue leftState rightValue rightState accepted form allocation leftAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateExpressionId allocation).inferExprFuel leftAccepted
  | @expression_conditional_condition fuel context source expected initial allocated final id value condition thenBranch elseBranch question colon conditionValue conditionState accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_conditional_then fuel context source expected initial allocated final id value condition thenBranch elseBranch question colon conditionValue conditionState thenValue thenState accepted form allocation conditionAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateExpressionId allocation).inferExprFuel conditionAccepted
  | @expression_conditional_else fuel context source expected initial allocated final id value condition thenBranch elseBranch question colon conditionValue conditionState thenValue elseValue thenState elseState accepted form allocation conditionAccepted thenAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact ((origins.allocateExpressionId allocation).inferExprFuel conditionAccepted).inferExprFuel thenAccepted
  | @expression_lambda_body fuel context source expected initial allocated final id value keyword parameters annotation body boundParameters parameterTypes parameterState bodyState resultType bodyResult accepted form allocation parametersAccepted prefixFacts child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact lambdaPrefix prefixFacts (lambdaParameters parametersAccepted (origins.allocateExpressionId allocation))
  | @expression_index_base fuel context source expected initial allocated final id value base key brackets inferred childFinal accepted form allocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_index_key fuel context source expected initial allocated final id value base key brackets baseValue keyValue baseState keyState valueState fitted childFinal keyType valueType accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have baseOrigins := (origins.allocateExpressionId allocation).inferExprFuel baseAccepted
    have keyOrigins : ActiveBinderCaptureOrigins keyState whole := by
      have same : keyState = baseState.fresh.2 := (congrArg Prod.snd keyFresh).symm
      rw [same]
      exact baseOrigins.congr_localBinders rfl
    have valueOrigins : ActiveBinderCaptureOrigins valueState whole := by
      have same : valueState = keyState.fresh.2 := (congrArg Prod.snd valueFresh).symm
      rw [same]
      exact keyOrigins.congr_localBinders rfl
    exact valueOrigins.unify fitting
  | @expression_call_constructor fuel context source expected initial allocated final id value callee arguments dataType constructor instantiation instantiated childFinal inferred accepted form allocation selected fresh child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact freshConstructor (origins.allocateExpressionId allocation) fresh
  | @expression_call_arguments fuel context source expected initial allocated final id value callee arguments values childFinal accepted form allocation nonconstructor child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_call_callee fuel context source expected initial allocated final id value callee arguments values argumentState childFinal inferred accepted form allocation nonconstructor argumentsAccepted indirect child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (origins.allocateExpressionId allocation).inferExprsFuel argumentsAccepted
  | @expression_contextual_constructor fuel context source expected initial allocated final id value dot name arguments dataType constructor typeArguments inferred childFinal accepted form allocation selected child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateExpressionId allocation
  | @expression_field_constructor fuel context source expected initial allocated final id value base dot name dataType constructor instantiation instantiated childFinal inferred accepted form allocation selected fresh child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact freshConstructor (origins.allocateExpressionId allocation) fresh
  | @matchCases_body fuel context scrutineeType expectedReturn saved arm arms initial patternState pattern result body accepted patternAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact ActualCaptureOrigins.pattern patternAccepted origins
  | @matchCases_tail fuel context scrutineeType expectedReturn saved arm arms initial patternState pattern result body tail accepted patternAccepted bodyAccepted child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have savedEq : initial.lexicalScope = saved := inputs.bounds.2.2
    rw [← savedEq]
    exact origins.restoreLexicalScope
  | @statement_match_single fuel context source expectedReturn initial allocated id result scrutinees arms scrutinee value childFinal accepted form allocation single child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_match_many fuel context source expectedReturn initial allocated id result scrutinees arms values childFinal accepted form allocation multiple child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact origins.allocateStatementId allocation
  | @statement_match_cases fuel context source expectedReturn initial allocated id result scrutinees arms scrutinee scrutineeState hiddenState hidden checked accepted form allocation scrutineeAccepted hiddenAllocation child =>
    dsimp only [CallIndex.initial] at origins ⊢
    exact (ActualCaptureOrigins.scrutinee scrutineeAccepted (origins.allocateStatementId allocation)).allocateHiddenLocal hiddenAllocation
  | @statement_match_default fuel context source expectedReturn initial allocated id result scrutinees arms scrutinee scrutineeState hiddenState hidden checked body bodyResult accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
    dsimp only [CallIndex.initial] at origins ⊢
    have hiddenOrigins := (ActualCaptureOrigins.scrutinee scrutineeAccepted (origins.allocateStatementId allocation)).allocateHiddenLocal hiddenAllocation
    exact of_scope hiddenOrigins (inferMatchCasesFuel_success_lexicalScope_eq rfl casesAccepted)

end Solcore.SourceSemantics.SourceInferenceExecution
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualInitializedBinderAllocation
/-! The same eleven accepted inference families preserve recorded binder
allocation bounds through the existing generalization-event proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open LocalGeneralizationBoundaries

theorem CallIndex.boundaryProgress {call : CallIndex}
    (inputs : call.Inputs) (accepted : call.Accepted) :
    LocalGeneralizationBoundaries.Progress call.initial call.final := by
  cases call with
  | expression => exact inferExprFuel_boundaries_progress accepted
  | constructorApplication => exact inferConstructorApplicationFuel_boundaries_progress accepted
  | constructorArguments => exact inferConstructorArgumentsFuel_boundaries_progress accepted
  | statements => exact inferStatementsFuel_boundaries_progress accepted
  | statement => exact inferStatementFuel_boundaries_progress accepted
  | forItems => exact inferForItemsFuel_boundaries_progress accepted
  | forItem => exact inferForItemFuel_boundaries_progress accepted
  | place => exact inferPlaceFuel_boundaries_progress accepted
  | assignedValue => exact inferAssignedValueFuel_boundaries_progress accepted
  | expressions => exact inferExprsFuel_boundaries_progress accepted
  | matchCases fuel context scrutinee expected saved cases initial result =>
    have scope : initial.lexicalScope = saved := inputs.bounds.2.2
    have subset : saved.binders ⊆ initial.localBinders := by
      rw [← scope]
      exact fun _ member => member
    exact inferMatchCasesFuel_boundaries_progress subset accepted

theorem CallIndex.initializedAllocated {call : CallIndex}
    (inputs : call.Inputs) (accepted : call.Accepted)
    (ready : LocalGeneralizationEvents.Ready call.initial)
    (below : call.initial.LocalBindersBelowNextLocal)
    (allocated : InitializedBindersAllocated call.initial) :
    InitializedBindersAllocated call.final :=
  (call.boundaryProgress inputs accepted).initializedAllocated ready below allocated

private theorem item_collector (item : ForItemForm) :
    item.initializedLetBinders = (forItemInitializedLetBindings item).map (·.binder) := by
  cases item with
  | letDecl _ initializer => cases initializer <;> rfl
  | expression | assignValue | assignBitNot => rfl

private theorem statement_collector (form : StatementForm) :
    form.initializedLetBinders = (statementInitializedLetBindings form).map (·.binder) := by
  cases form with
  | letDecl _ initializer => cases initializer <;> rfl
  | forLoop =>
    simp only [StatementForm.initializedLetBinders, statementInitializedLetBindings,
      List.map_append, List.map_flatMap, ← item_collector]
  | returnStmt | expression | assignValue | assignBitNot | ifThen | block
  | matchWith | whileLoop | breakStmt | continueStmt => rfl

/-- The operational inventory bound applies to the semantic initialized binding
collector without changing either collector's identities. -/
theorem initialized_binding_allocated {state : State}
    (allocated : InitializedBindersAllocated state)
    {binding : InitializedLetBinding}
    (member : binding ∈ initializedLetBindings (state.toTypedSource [])) :
    binding.binder.id.binderIndex ≤ state.nextLocal := by
  obtain ⟨node, present, bound⟩ := List.mem_flatMap.mp member
  cases node with
  | expression _ => cases bound
  | statement statement =>
    apply allocated (.statement statement) present binding.binder
    change binding.binder ∈ statement.form.initializedLetBinders
    rw [statement_collector]
    exact List.mem_map.mpr ⟨binding, bound, rfl⟩

end Solcore.SourceSemantics.SourceInferenceExecution
end
