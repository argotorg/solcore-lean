import Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorInterval
import Solcore.SourceSemantics.SourceInferenceActualIndirectCallPrefix
import Solcore.SourceSemantics.SourceInferenceActualMatchCompletion

/-! The actual suffix of each child call cannot move the local ID allocator backwards. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

private theorem exceptPure_eq_ok {epsilon alpha : Type} (value result : alpha) :
    ((pure value : Except epsilon alpha) = .ok result) ↔ value = result := by
  change (Except.ok value = Except.ok result) ↔ value = result
  simp

private theorem exceptThrow_ne_ok {epsilon alpha : Type} (error : epsilon) (value : alpha) :
    (throw error : Except epsilon alpha) ≠ .ok value := by
  intro impossible
  cases impossible

private theorem constructor_arguments_local {fuel : Nat} {context : SourceInference.Context}
    {sources : List Syntax.Expr} {expected : List Ty} {before : State}
    {result : List InferredExpression × State}
    (accepted : inferConstructorArgumentsFuel fuel context sources expected before = .ok result) :
    before.nextLocal ≤ result.2.nextLocal :=
  (LocalReadScopeProgress.inferConstructorArgumentsFuel_scope_progress accepted).next

private theorem builtin_local {source callee : Syntax.Expr} {name : String}
    {function : BuiltinFunctionId} {arguments : List InferredExpression}
    {id : ExpressionId} {expected : Option Ty} {before : State}
    {result : InferredExpression × State}
    (accepted : recordBuiltinFunctionCall source callee name function arguments id expected before = .ok result) :
    before.nextLocal ≤ result.2.nextLocal :=
  (LocalReadScopeProgress.Progress.recordBuiltinFunctionCall accepted).next

private theorem attached_local (state : State) (entries : List ExpressionCoercions) :
    (attachExpressionCoercions state entries).nextLocal = state.nextLocal := by
  unfold attachExpressionCoercions
  induction entries generalizing state with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact ih _

open Lean Meta Elab Tactic in
elab "collect_suffix_allocator" : tactic => withMainContext do
  evalTactic (← `(tactic| collect_local_allocator))
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [``constructor_arguments_local, ``builtin_local] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved local suffix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "local_suffix_order") proof
        setGoals [next]
      catch _ => saved.restore

private theorem lambdaPrefix_unique
    {context : SourceInference.Context} {expected : Option Ty}
    {annotation : Option Syntax.TypeExpr} {types : List Ty} {initial : State}
    {leftType rightType : Ty} {leftState rightState : State}
    (left : LambdaPrefixFacts context expected annotation types initial leftType leftState)
    (right : LambdaPrefixFacts context expected annotation types initial rightType rightState) :
    leftType = rightType ∧ leftState = rightState := by
  cases left <;> cases right <;> simp_all

private theorem match_scrutinee_local_suffix
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr} {arms : Syntax.MatchArms}
    {expectedReturn : Ty} {initial allocated : State} {id : StatementId}
    {scrutinee : InferredExpression} {scrutineeState : State} {result : StatementResult}
    (accepted : inferStatementFuel (fuel+1) context source expectedReturn initial = .ok result)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated = .ok (scrutinee, scrutineeState)) :
    scrutineeState.nextLocal ≤ result.state.nextLocal := by
  have completion := matchCompletion_accepted form allocation scrutineeAccepted
    (show scrutineeState.allocateHiddenLocal =
      (scrutineeState.allocateHiddenLocal.1, scrutineeState.allocateHiddenLocal.2) from rfl) accepted
  unfold matchCompletion at completion
  simp only [bind, Except.bind] at completion
  repeat' first | split at completion
  all_goals try cases completion
  all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
  all_goals collect_suffix_allocator
  all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq]
  all_goals try subst_vars
  all_goals simp_all only [State.recordNode, State.allocateHiddenLocal, State.restoreLexicalScope]
  all_goals omega

/-- The repeated suffix inversion only inspects the accepted parent run and
uses previously proved allocator monotonicity for its remaining recursive calls. -/
macro "finish_local_suffix" accepted:ident : tactic => `(tactic|
  first |
    all_goals try simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure]
    all_goals repeat' first | split at $accepted:ident
    all_goals try cases $accepted:ident
    all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
    all_goals collect_suffix_allocator
    all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq]
    all_goals try subst_vars
    all_goals try simp_all only [CallIndex.final, State.allocateExpressionId_nextLocal,
      State.allocateStatementId_nextLocal, attached_local]
    all_goals try simp_all only [CallIndex.final, attached_local, State.allocateBinder,
      State.allocateHiddenLocal, State.allocateExpressionId, State.allocateStatementId,
      State.restoreLexicalScope, State.recordNode, State.fresh,
      State.addRequirementWithId, State.addRequirementsWithIds,
      recordExpression, recordSelectedCall, recordSelectedCallResult, recordIndirectCall]
    all_goals omega)

theorem ChildStep.local_suffix {parent child : CallIndex} (step : ChildStep parent child) :
    child.final.nextLocal ≤ parent.final.nextLocal := by
  cases step with
  | expression_group accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_tuple accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expressions_head accepted head =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprsFuel at accepted
      finish_local_suffix accepted
  | expressions_tail accepted head tail =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprsFuel at accepted
      finish_local_suffix accepted
  | statements_head accepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementsFuel at accepted
      finish_local_suffix accepted
  | statements_tail accepted nonempty headAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementsFuel at accepted
      finish_local_suffix accepted
  | statement_initializer accepted form allocation annotation child =>
      cases annotation
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_return accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_expression accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_block accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_if_condition accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_if_then accepted form allocation conditionAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_if_else accepted form allocation conditionAccepted hasElse thenAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_assignment accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_bitnot accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_while_condition accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_while_body accepted form allocation conditionAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_for_initializer accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_for_condition accepted form allocation initializerAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_for_body accepted form allocation initializerAccepted conditionAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | statement_for_post accepted form allocation initializerAccepted conditionAccepted bodyAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | forItems_head accepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemsFuel at accepted
      finish_local_suffix accepted
  | forItems_tail accepted headAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemsFuel at accepted
      finish_local_suffix accepted
  | forItem_initializer accepted form annotation child =>
      cases annotation
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemFuel at accepted
      finish_local_suffix accepted
  | forItem_expression accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemFuel at accepted
      finish_local_suffix accepted
  | forItem_assignment accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemFuel at accepted
      finish_local_suffix accepted
  | forItem_bitnot accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferForItemFuel at accepted
      finish_local_suffix accepted
  | assignedValue_place accepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals try simp only [CallIndex.Accepted, inferAssignedValueFuel] at accepted
      finish_local_suffix accepted
  | @assignedValue_value fuel context target value operator initial final targetState
      assignment inferred place fitted childFinal childValue accepted targetAccepted fitting child =>
      cases operator
      all_goals simp only [CallIndex.Accepted, assignmentExpected] at *
      all_goals try (simp only [pure, Pure.pure, Except.pure, Except.ok.injEq] at fitting; subst fitted)
      all_goals change inferAssignedValueFuel fuel context target _ value initial = .ok _ at accepted
      all_goals unfold inferAssignedValueFuel at accepted
      all_goals simp_all only [bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq]
      all_goals simp_all only [CallIndex.final]
      all_goals exact Nat.le_refl _
  | place_group accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferPlaceFuel at accepted
      finish_local_suffix accepted
  | place_index_base accepted form child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferPlaceFuel at accepted
      finish_local_suffix accepted
  | place_index_key accepted form baseAccepted keyFresh valueFresh fitting child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferPlaceFuel at accepted
      finish_local_suffix accepted
  | constructorApplication_arguments accepted arity fitting child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals simp only [CallIndex.Accepted, inferConstructorApplicationFuel] at accepted
      finish_local_suffix accepted
  | constructorArguments_head accepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferConstructorArgumentsFuel at accepted
      finish_local_suffix accepted
  | constructorArguments_tail accepted headAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferConstructorArgumentsFuel at accepted
      finish_local_suffix accepted
  | expression_unary accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_binary_left accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_binary_right accepted form allocation leftAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_conditional_condition accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_conditional_then accepted form allocation conditionAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_conditional_else accepted form allocation conditionAccepted thenAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_lambda_body accepted form allocation parametersAccepted prefixFacts child =>
      obtain ⟨parameters, types, parameterState, resultType, resultState, bodyResult,
        unifiedState, restoredState, parametersRun, actualPrefix, bodyRun, unified, restored, recorded⟩ :=
        inferExprFuel_success_lambda_facts form allocation accepted
      cases Except.ok.inj (parametersRun.symm.trans parametersAccepted)
      obtain ⟨sameType, sameState⟩ := lambdaPrefix_unique actualPrefix prefixFacts
      cases sameType
      cases sameState
      cases Except.ok.inj (bodyRun.symm.trans child)
      have after := localReadScope_unify_preserves_nextLocal unified
      have finish := localReadScope_recordExpressionWithExpected_nextLocal recorded
      simp only [restored, State.restoreLexicalScope_nextLocal] at finish
      simpa only [CallIndex.final] using Nat.le_of_eq (finish.trans after).symm
  | expression_index_base accepted form allocation child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_index_key accepted form allocation baseAccepted keyFresh valueFresh fitting child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_call_constructor accepted form allocation selected fresh child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_call_arguments accepted form allocation nonconstructor child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | @expression_call_callee fuel context source expected initial allocated final id value
      callee arguments values argumentState childFinal inferred
      accepted form allocation nonconstructor argumentsAccepted indirect child =>
      obtain ⟨application, applicationRun, recorded⟩ :=
        indirectCall_actual_suffix form allocation nonconstructor argumentsAccepted indirect child accepted
      have after := localReadScope_applyFunctionType_nextLocal applicationRun
      have finish := (LocalReadScopeProgress.Progress.recordIndirectCall source inferred values application).next
      rw [recorded] at finish
      exact Nat.le_trans (Nat.le_of_eq after.symm) finish
  | expression_contextual_constructor accepted form allocation selected child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | expression_field_constructor accepted form allocation selected fresh child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferExprFuel at accepted
      finish_local_suffix accepted
  | matchCases_body accepted patternAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferMatchCasesFuel at accepted
      finish_local_suffix accepted
  | matchCases_tail accepted patternAccepted bodyAccepted child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferMatchCasesFuel at accepted
      finish_local_suffix accepted
  | statement_match_single accepted form allocation single child =>
      all_goals simp only [CallIndex.Accepted] at *
      all_goals unfold inferStatementFuel at accepted
      finish_local_suffix accepted
  | @statement_match_many fuel context source expectedReturn initial allocated id result
      scrutinees arms values childFinal accepted form allocation multiple child =>
      simp only [CallIndex.Accepted] at accepted child
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
      have after := match_scrutinee_local_suffix accepted form allocation scrutineeAccepted
      have same : tupleState.nextLocal = childFinal.nextLocal := rfl
      simpa only [same, CallIndex.final] using after
  | statement_match_cases accepted form allocation scrutineeAccepted hiddenAllocation child =>
      have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
      simp only [CallIndex.Accepted] at child
      unfold matchCompletion at completion
      simp only [child, bind, Except.bind] at completion
      repeat' first | split at completion
      all_goals try cases completion
      all_goals try simp_all only [exceptPure_eq_ok, exceptThrow_ne_ok]
      all_goals collect_suffix_allocator
      all_goals try simp_all only [Except.ok.injEq, Prod.mk.injEq]
      all_goals try subst_vars
      all_goals simp_all only [CallIndex.final, State.recordNode, State.restoreLexicalScope]
      all_goals omega
  | statement_match_default accepted form allocation scrutineeAccepted hiddenAllocation casesAccepted default child =>
      have completion := matchCompletion_accepted form allocation scrutineeAccepted hiddenAllocation accepted
      simp only [CallIndex.Accepted] at child
      unfold matchCompletion at completion
      simp only [casesAccepted, default, child, bind, Except.bind, pure, Pure.pure, Except.pure] at completion
      split at completion
      · contradiction
      · cases Except.ok.inj completion
        exact Nat.le_refl _
/-- Every actual descendant occupies an interval inside its accepted root call. -/
theorem CallOccurrence.local_interval {root call : CallIndex}
    (here : CallOccurrence root call) :
    root.initial.nextLocal ≤ call.initial.nextLocal ∧
      call.final.nextLocal ≤ root.final.nextLocal := by
  induction here with
  | root _ => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | child _ step ih =>
      exact ⟨Nat.le_trans ih.1 step.local_prefix, Nat.le_trans step.local_suffix ih.2⟩

end Solcore.SourceSemantics.SourceInferenceExecution
