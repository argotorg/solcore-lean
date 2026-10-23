import Lean
import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.Frontend.SourceInference.DirectRequirementInference

/-! Direct requirement allocation follows the genuine prefixes of recursive
calls, including completed siblings and the actual saved lexical scopes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open State (DirectRequirementsProgress)

private theorem allocated_expression {before after : State} {id : ExpressionId}
    (accepted : before.allocateExpressionId = (id, after)) :
    DirectRequirementsProgress before after := by
  have same : after = before.allocateExpressionId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact .refl _
private theorem allocated_statement {before after : State} {id : StatementId}
    (accepted : before.allocateStatementId = (id, after)) :
    DirectRequirementsProgress before after := by
  have same : after = before.allocateStatementId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact .refl _
private theorem allocated_fresh {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    DirectRequirementsProgress before after := by
  have same : after = before.fresh.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact .refl _
private theorem allocated_hidden {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    DirectRequirementsProgress before after := by
  have same : after = before.allocateHiddenLocal.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact .refl _
private theorem allocated_constructor {before after : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (accepted : freshDataConstructorInstantiation dataType constructor before = (instantiation, after)) :
    DirectRequirementsProgress before after := by
  simpa only [accepted] using
    freshDataConstructorInstantiation_direct_progress dataType constructor before

private theorem lambda_prefix {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {before after : State} {resultType : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters before resultType after) :
    DirectRequirementsProgress before after := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact .refl _
  | noExpectedPartsFresh _ _ allocated => exact allocated_fresh allocated
  | expectedPartsAnnotated _ unified => exact unify_direct_progress unified
  | expectedPartsInferred _ unified => exact unify_direct_progress unified

private theorem scrutinee_prefix {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {before : State}
    {result : InferredExpression × State}
    (accepted : matchScrutinee fuel context span sources before = .ok result) :
    DirectRequirementsProgress before result.2 := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_direct_progress accepted
  · cases child : inferExprsFuel fuel context sources before with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok value =>
      have progress := inferExprsFuel_direct_progress child
      simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact progress

open Lean Meta Elab Tactic in
elab "collect_direct_prefix" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [
      ``allocated_expression, ``allocated_statement, ``allocated_fresh, ``allocated_hidden,
      ``allocated_constructor, ``lambda_prefix, ``scrutinee_prefix,
      ``inferExprFuel_direct_progress, ``inferExprsFuel_direct_progress,
      ``inferStatementsFuel_direct_progress, ``inferStatementFuel_direct_progress,
      ``inferForItemsFuel_direct_progress, ``inferForItemFuel_direct_progress,
      ``inferPlaceFuel_direct_progress, ``inferMatchCasesFuel_direct_progress,
      ``inferMatchPatternFuel_direct_progress, ``bindLambdaParameters_direct_progress,
      ``unify_direct_progress] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved direct prefix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "direct_prefix") proof
        setGoals [next]
      catch _ => saved.restore

theorem ChildStep.direct_prefix {parent child : CallIndex} (step : ChildStep parent child) :
    DirectRequirementsProgress parent.initial child.initial := by
  cases step
  case assignedValue_value accepted targetAccepted fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_direct_prefix
    all_goals simp only [CallIndex.initial]
    all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
      [DirectRequirementsProgress.trans, DirectRequirementsProgress.refl]
  case constructorApplication_arguments accepted arity fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_direct_prefix
    all_goals simp only [CallIndex.initial]
    all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
      [DirectRequirementsProgress.trans, DirectRequirementsProgress.refl]
  all_goals collect_direct_prefix
  all_goals simp only [CallIndex.initial]
  all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
    [DirectRequirementsProgress.trans, DirectRequirementsProgress.refl]
  case statement_if_else =>
    exact (allocated_statement (by assumption)).trans
      ((inferExprFuel_direct_progress (by assumption)).trans
        (inferStatementsFuel_direct_progress (by assumption)))
  case statement_for_post =>
    exact (allocated_statement (by assumption)).trans
      ((inferForItemsFuel_direct_progress (by assumption)).trans
        ((inferExprFuel_direct_progress (by assumption)).trans
          (inferStatementsFuel_direct_progress (by assumption))))
  case expression_index_key =>
    exact (allocated_expression (by assumption)).trans
      ((inferExprFuel_direct_progress (by assumption)).trans
        ((allocated_fresh (by assumption)).trans
          ((allocated_fresh (by assumption)).trans (unify_direct_progress (by assumption)))))
  case matchCases_tail =>
    exact (inferMatchPatternFuel_direct_progress (by assumption)).trans
      (inferStatementsFuel_direct_progress (by assumption))

theorem CallOccurrence.direct_prefix {root call : CallIndex} (here : CallOccurrence root call) :
    DirectRequirementsProgress root.initial call.initial := by
  induction here with
  | root _ => exact .refl _
  | child _ step ih => exact ih.trans step.direct_prefix

end Solcore.SourceSemantics.SourceInferenceExecution
