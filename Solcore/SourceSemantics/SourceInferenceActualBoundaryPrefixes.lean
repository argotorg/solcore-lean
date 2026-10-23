import Lean
import Solcore.SourceSemantics.SourceInferenceActualCallInputTraversal
import Solcore.SourceSemantics.SourceInferenceActualInitializedBinderAllocation

/-! Genuine child entries inherit bounded generalization progress from the
actual allocation and completed sibling prefixes of the same parent call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail
open LocalGeneralizationBoundaries

private theorem allocated_expression {before after : State} {id : ExpressionId}
    (accepted : before.allocateExpressionId = (id, after)) :
    Progress before after := by
  have same : after = before.allocateExpressionId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact Progress.allocateExpressionId _
private theorem allocated_statement {before after : State} {id : StatementId}
    (accepted : before.allocateStatementId = (id, after)) :
    Progress before after := by
  have same : after = before.allocateStatementId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact Progress.allocateStatementId _
private theorem allocated_fresh {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    Progress before after := by
  have same : after = before.fresh.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact Progress.fresh _
private theorem allocated_hidden {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    Progress before after := by
  have same : after = before.allocateHiddenLocal.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact Progress.allocateHiddenLocal _
private theorem allocated_constructor {before after : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (accepted : freshDataConstructorInstantiation dataType constructor before = (instantiation, after)) :
    Progress before after := by
  simpa only [accepted] using
    Progress.freshDataConstructorInstantiation dataType constructor before

private theorem lambda_prefix {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {parameters : List Ty} {before after : State} {resultType : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation parameters before resultType after) :
    Progress before after := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact .refl _
  | noExpectedPartsFresh _ _ allocated => exact allocated_fresh allocated
  | expectedPartsAnnotated _ unified => exact Progress.unify unified
  | expectedPartsInferred _ unified => exact Progress.unify unified

private theorem scrutinee_prefix {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {before : State}
    {result : InferredExpression × State}
    (accepted : matchScrutinee fuel context span sources before = .ok result) :
    Progress before result.2 := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_boundaries_progress accepted
  · cases child : inferExprsFuel fuel context sources before with
    | error error => simp [child, bind, Except.bind] at accepted
    | ok value =>
      have progress := inferExprsFuel_boundaries_progress child
      simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact progress.trans ((Progress.allocateExpressionId _).trans
        (Progress.recordExpression _ _ (by intro _ _ impossible; cases impossible)))

open Lean Meta Elab Tactic in
elab "collect_boundary_prefix" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [
      ``allocated_expression, ``allocated_statement, ``allocated_fresh, ``allocated_hidden,
      ``allocated_constructor, ``lambda_prefix, ``scrutinee_prefix,
      ``inferExprFuel_boundaries_progress, ``inferExprsFuel_boundaries_progress,
      ``inferStatementsFuel_boundaries_progress, ``inferStatementFuel_boundaries_progress,
      ``inferForItemsFuel_boundaries_progress, ``inferForItemFuel_boundaries_progress,
      ``inferPlaceFuel_boundaries_progress,
      ``Progress.inferMatchPatternFuel, ``Progress.bindLambdaParameters,
      ``Progress.unify] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved direct prefix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "boundaries_prefix") proof
        setGoals [next]
      catch _ => saved.restore

theorem ChildStep.boundaries_prefix {parent child : CallIndex} (inputs : parent.Inputs) (step : ChildStep parent child) :
    Progress parent.initial child.initial := by
  cases step
  case assignedValue_value accepted targetAccepted fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_boundary_prefix
    all_goals simp only [CallIndex.initial]
    all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
      [Progress.trans, Progress.refl]
  case constructorApplication_arguments accepted arity fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_boundary_prefix
    all_goals simp only [CallIndex.initial]
    all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
      [Progress.trans, Progress.refl]
  all_goals collect_boundary_prefix
  all_goals simp only [CallIndex.initial]
  all_goals try solve_by_elim (maxDepth := 8) (transparency := .reducible)
    [Progress.trans, Progress.refl]
  case statement_if_else =>
    exact (allocated_statement (by assumption)).trans
      ((inferExprFuel_boundaries_progress (by assumption)).trans
        ((inferStatementsFuel_boundaries_progress (by assumption)).restore _
          (fun _ member => member)))
  case statement_for_post =>
    exact (allocated_statement (by assumption)).trans
      ((inferForItemsFuel_boundaries_progress (by assumption)).trans
        (((inferExprFuel_boundaries_progress (by assumption)).trans
          (inferStatementsFuel_boundaries_progress (by assumption))).restore _
          (fun _ member => member)))
  case expression_index_key =>
    exact (allocated_expression (by assumption)).trans
      ((inferExprFuel_boundaries_progress (by assumption)).trans
        ((allocated_fresh (by assumption)).trans
          ((allocated_fresh (by assumption)).trans (Progress.unify (by assumption)))))
  case matchCases_tail =>
    have scope := inputs.bounds.2.2
    exact ((Progress.inferMatchPatternFuel (by assumption)).trans
      (inferStatementsFuel_boundaries_progress (by assumption))).restore _
      (by rw [← scope]; exact fun _ member => member)
  case statement_match_default =>
    exact (allocated_statement (by assumption)).trans
      ((scrutinee_prefix (by assumption)).trans
        ((allocated_hidden (by assumption)).trans
          (inferMatchCasesFuel_boundaries_progress (fun _ member => member) (by assumption))))

theorem CallOccurrence.boundaries_prefix {root call : CallIndex} (inputs : root.Inputs) (here : CallOccurrence root call) :
    Progress root.initial call.initial := by
  induction here with
  | root _ => exact .refl _
  | child path step ih => exact ih.trans (step.boundaries_prefix (path.inputs inputs))

end Solcore.SourceSemantics.SourceInferenceExecution
