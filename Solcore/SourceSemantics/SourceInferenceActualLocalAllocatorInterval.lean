import Lean
import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.Frontend.SourceInference.LocalReadScopeInference

/-! Local identities use `nextLocal`, independently of the type metavariable
allocator. Actual call prefixes and suffixes preserve its ordering. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

theorem CallIndex.local_next {call : CallIndex} (accepted : call.Accepted) :
    call.initial.nextLocal ≤ call.final.nextLocal := by
  cases call with
  | expression => exact inferExprFuel_nextLocal_le accepted
  | constructorApplication =>
      exact (LocalReadScopeProgress.inferConstructorApplicationFuel_scope_progress accepted).next
  | constructorArguments =>
      exact (LocalReadScopeProgress.inferConstructorArgumentsFuel_scope_progress accepted).next
  | statement => exact inferStatementFuel_nextLocal_le accepted
  | statements => exact inferStatementsFuel_nextLocal_le accepted
  | forItem => exact inferForItemFuel_nextLocal_le accepted
  | forItems => exact inferForItemsFuel_nextLocal_le accepted
  | place => exact (LocalReadScopeProgress.inferPlaceFuel_scope_progress accepted).next
  | assignedValue => exact (LocalReadScopeProgress.inferAssignedValueFuel_scope_progress accepted).next
  | expressions => exact inferExprsFuel_nextLocal_le accepted
  | matchCases => exact inferMatchCasesFuel_nextLocal_le accepted

private theorem allocated_expression {before after : State} {id : ExpressionId}
    (accepted : before.allocateExpressionId = (id, after)) :
    after.nextLocal = before.nextLocal := by
  exact (congrArg (fun result : ExpressionId × State => result.2.nextLocal) accepted).symm

private theorem allocated_statement {before after : State} {id : StatementId}
    (accepted : before.allocateStatementId = (id, after)) :
    after.nextLocal = before.nextLocal := by
  exact (congrArg (fun result : StatementId × State => result.2.nextLocal) accepted).symm

private theorem fresh_local {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    after.nextLocal = before.nextLocal := by
  exact (congrArg (fun result : Ty × State => result.2.nextLocal) accepted).symm

private theorem hidden_local {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    before.nextLocal ≤ after.nextLocal := by
  have same := congrArg (fun result : Resolved.LocalId × State => result.2.nextLocal) accepted
  simp only [State.allocateHiddenLocal] at same
  omega

private theorem constructor_local {data : ProgramDataSignature}
    {constructor : ProgramDataConstructorSignature} {before after : State}
    {instantiation : DataConstructorInstantiation}
    (accepted : freshDataConstructorInstantiation data constructor before = (instantiation, after)) :
    before.nextLocal ≤ after.nextLocal := by
  have result := (LocalReadScopeProgress.Progress.freshDataConstructorInstantiation data constructor before).next
  simpa only [accepted] using result

private theorem place_local {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Expr} {before : State} {result : PlaceResolution × State}
    (accepted : inferPlaceFuel fuel context source before = .ok result) :
    before.nextLocal ≤ result.2.nextLocal :=
  (LocalReadScopeProgress.inferPlaceFuel_scope_progress accepted).next

private theorem assigned_local {fuel : Nat} {context : SourceInference.Context}
    {target source : Syntax.Expr} {operator : Syntax.ValueAssignOp} {before : State}
    {result : AssignmentResolution × InferredExpression × State}
    (accepted : inferAssignedValueFuel fuel context target operator source before = .ok result) :
    before.nextLocal ≤ result.2.2.nextLocal :=
  (LocalReadScopeProgress.inferAssignedValueFuel_scope_progress accepted).next

private theorem scrutinee_local {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {before : State}
    {result : InferredExpression × State}
    (accepted : matchScrutinee fuel context span sources before = .ok result) :
    before.nextLocal ≤ result.2.nextLocal := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_nextLocal_le accepted
  · cases child : inferExprsFuel fuel context sources before with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok value =>
      have next := inferExprsFuel_nextLocal_le child
      simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact next

private theorem lambda_prefix_local {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {before after : State} {resultType : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters before resultType after) :
    before.nextLocal = after.nextLocal := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => rfl
  | noExpectedPartsFresh _ _ allocated => exact (fresh_local allocated).symm
  | expectedPartsAnnotated _ unified => exact (localReadScope_unify_preserves_nextLocal unified).symm
  | expectedPartsInferred _ unified => exact (localReadScope_unify_preserves_nextLocal unified).symm

private theorem assignment_fitting_local {operator : Syntax.ValueAssignOp}
    {before after : State} {type : Ty}
    (accepted : (match operator with | .equal => pure before | _ => unify before type .word) =
      (Except.ok after : Except Error State)) : after.nextLocal = before.nextLocal := by
  cases operator
  all_goals first
  | (cases Except.ok.inj accepted; rfl)
  | exact localReadScope_unify_preserves_nextLocal accepted

private theorem constructor_fitting_local {expected : Option Ty}
    {before after : State} {type : Ty}
    (accepted : (match expected with | none => pure before | some target => unify before type target) =
      (Except.ok after : Except Error State)) : after.nextLocal = before.nextLocal := by
  cases expected
  · cases Except.ok.inj accepted; rfl
  · exact localReadScope_unify_preserves_nextLocal accepted

open Lean Meta Elab Tactic in
elab "collect_local_allocator" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [
      ``CallIndex.local_next, ``allocated_expression, ``allocated_statement,
      ``fresh_local, ``hidden_local, ``constructor_local, ``lambda_prefix_local,
      ``assignment_fitting_local, ``constructor_fitting_local,
      ``inferExprFuel_nextLocal_le, ``inferExprsFuel_nextLocal_le,
      ``inferStatementsFuel_nextLocal_le, ``inferStatementFuel_nextLocal_le,
      ``inferForItemsFuel_nextLocal_le, ``inferForItemFuel_nextLocal_le,
      ``inferMatchCasesFuel_nextLocal_le, ``inferMatchPatternFuel_nextLocal_le,
      ``place_local, ``assigned_local, ``scrutinee_local,
      ``localReadScope_bindLambdaParameters_nextLocal_le,
      ``localReadScope_unify_preserves_nextLocal,
      ``localReadScope_withExpected_nextLocal,
      ``localReadScope_recordExpressionWithExpected_nextLocal,
      ``localReadScope_inferUnaryOperator_nextLocal,
      ``localReadScope_inferBinaryOperator_nextLocal,
      ``localReadScope_selectFunctionCandidateFrom_nextLocal,
      ``localReadScope_applyFunctionType_nextLocal] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved local allocator"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "local_order") proof
        setGoals [next]
      catch _ => saved.restore

theorem ChildStep.local_prefix {parent child : CallIndex} (step : ChildStep parent child) :
    parent.initial.nextLocal ≤ child.initial.nextLocal := by
  cases step
  case assignedValue_value accepted targetAccepted fitting child =>
    split at fitting
    all_goals try (cases Except.ok.inj fitting)
    all_goals collect_local_allocator
    all_goals simp only [CallIndex.initial] at *
    all_goals omega
  case constructorApplication_arguments accepted arity fitting child =>
    split at fitting
    all_goals try (cases Except.ok.inj fitting)
    all_goals collect_local_allocator
    all_goals simp only [CallIndex.initial] at *
    all_goals omega
  all_goals collect_local_allocator
  all_goals simp only [CallIndex.initial, State.restoreLexicalScope_nextLocal] at *
  all_goals omega

end Solcore.SourceSemantics.SourceInferenceExecution
