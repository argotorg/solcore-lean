import Solcore.SourceSemantics.SourceInferenceActualLocalReadCutoff
import Solcore.SourceSemantics.SourceInferenceActualDirectRequirementPrefixes

/-! Every recursive child starts after actual state-producing prefixes.
Existing reads and completed sibling calls retain a real local-ID cutoff. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

namespace LocalReadCutoff
theorem transport {before after : State} (same : after.nodes = before.nodes)
    (next : before.nextLocal ≤ after.nextLocal) (cutoff : LocalReadCutoff before) :
    LocalReadCutoff after := by
  intro node member name binder form
  exact Nat.lt_of_lt_of_le (cutoff node (same ▸ member) name binder form) next

theorem restore {state : State} (cutoff : LocalReadCutoff state) (scope : LexicalScope) :
    LocalReadCutoff (state.restoreLexicalScope scope) := cutoff

private theorem allocated_expression {before after : State} {id : ExpressionId}
    (accepted : before.allocateExpressionId = (id, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = before.allocateExpressionId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact fun proof => proof
private theorem allocated_statement {before after : State} {id : StatementId}
    (accepted : before.allocateStatementId = (id, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = before.allocateStatementId.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact fun proof => proof
private theorem allocated_fresh {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = before.fresh.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact fun proof => proof
private theorem allocated_hidden {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = before.allocateHiddenLocal.2 := (congrArg Prod.snd accepted).symm
  rw [same]
  exact transport rfl (Nat.le_succ _)
private theorem allocated_constructor {before after : State}
    {dataType : ProgramDataSignature} {constructor : ProgramDataConstructorSignature}
    {instantiation : DataConstructorInstantiation}
    (accepted : freshDataConstructorInstantiation dataType constructor before = (instantiation, after)) :
    LocalReadCutoff before → LocalReadCutoff after := by
  have same : after = (freshDataConstructorInstantiation dataType constructor before).2 :=
    (congrArg Prod.snd accepted).symm
  rw [same]
  exact transport (freshDataConstructorInstantiation_nodes _ _ _)
    (LocalReadScopeProgress.Progress.freshDataConstructorInstantiation _ _ _).next
private theorem unified {before after : State} {left right : Ty}
    (accepted : unify before left right = .ok after) :
    LocalReadCutoff before → LocalReadCutoff after :=
  transport (unify_occurrenceState_eq accepted).1
    (Nat.le_of_eq (localReadScope_unify_preserves_nextLocal accepted).symm)
private theorem parameters {context : SourceInference.Context} {sources : List Syntax.LambdaParameter}
    {index : Nat} {seen : List String} {before : State} {result : List TypedBinder × List Ty × State}
    (accepted : bindLambdaParameters context sources index seen before = .ok result) :
    LocalReadCutoff before → LocalReadCutoff result.2.2 :=
  transport (bindLambdaParameters_occurrenceState_eq accepted).1
    (localReadScope_bindLambdaParameters_nextLocal_le accepted)
private theorem pattern {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Pattern}
    {expected : Ty} {before : State} {result : TypedMatchPattern × State}
    (accepted : inferMatchPatternFuel fuel context source expected before = .ok result) :
    LocalReadCutoff before → LocalReadCutoff result.2 :=
  transport (inferMatchPatternFuel_occurrenceState_eq accepted).1
    (inferMatchPatternFuel_nextLocal_le accepted)
private theorem lambda_prefix {context : SourceInference.Context}
    {expected : Option Ty} {annotation : Option Syntax.TypeExpr}
    {types : List Ty} {before after : State} {resultType : Ty}
    (prefixFacts : LambdaPrefixFacts context expected annotation types before resultType after) :
    LocalReadCutoff before → LocalReadCutoff after := by
  cases prefixFacts with
  | noExpectedPartsAnnotated => exact fun proof => proof
  | noExpectedPartsFresh _ _ allocated => exact allocated_fresh allocated
  | expectedPartsAnnotated _ accepted => exact unified accepted
  | expectedPartsInferred _ accepted => exact unified accepted

/-- Each prior call uses the inputs and stable binder bounds derived from the
same genuine parent edge. The implication is consumed in execution order. -/
private theorem child_transition {parent child : CallIndex}
    (inputs : parent.Inputs) (below : parent.initial.LocalBindersBelowNextLocal)
    (allocated : parent.initial.DirectRequirementsAllocated)
    (step : ChildStep parent child) :
    LocalReadCutoff child.initial → LocalReadCutoff child.final :=
  CallIndex.localReadCutoff step.child_accepted (step.inputs inputs)
    (ActualLocalAllocator.child_bound inputs below step)
    (step.direct_prefix.allocated inputs.wellFormed allocated)

private theorem match_prefix {fuel : Nat} {context : SourceInference.Context}
    {source : Syntax.Statement} {expected : Ty} {initial allocated : State} {id : StatementId}
    {result : StatementResult} {scrutinees : Syntax.NonemptyDelimitedList Syntax.Expr}
    {arms : Syntax.MatchArms} {value : InferredExpression} {final : State}
    (inputs : (CallIndex.statement (fuel + 1) context source expected initial result).Inputs)
    (below : initial.LocalBindersBelowNextLocal)
    (direct : initial.DirectRequirementsAllocated) (previous : LocalReadCutoff initial)
    (accepted : (CallIndex.statement (fuel + 1) context source expected initial result).Accepted)
    (form : source.value = .matchWith scrutinees arms)
    (allocation : initial.allocateStatementId = (id, allocated))
    (scrutineeAccepted : matchScrutinee fuel context source.span scrutinees.elements.toList allocated =
      .ok (value, final)) : LocalReadCutoff final := by
  have allocatedCutoff := allocated_statement allocation previous
  unfold matchScrutinee at scrutineeAccepted
  split at scrutineeAccepted
  · have step := ChildStep.statement_match_single accepted form allocation
      (by assumption) scrutineeAccepted
    exact child_transition inputs below direct step allocatedCutoff
  · cases inferred : inferExprsFuel fuel context scrutinees.elements.toList allocated with
    | error error => simp [inferred, bind, Except.bind] at scrutineeAccepted
    | ok pair =>
      have step := ChildStep.statement_match_many accepted form allocation
        (by assumption) inferred
      have cutoff := child_transition inputs below direct step allocatedCutoff
      simp only [inferred, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq]
        at scrutineeAccepted
      cases scrutineeAccepted
      intro node member name binder localForm
      simp only [State.recordNode, List.mem_append, List.mem_singleton] at member
      rcases member with old | new
      · exact cutoff node old name binder localForm
      · cases Node.expression.inj new
        cases localForm

open Lean Meta Elab Tactic in
elab "collect_cutoff_prefix" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [
      ``allocated_expression, ``allocated_statement, ``allocated_fresh, ``allocated_hidden,
      ``allocated_constructor, ``unified, ``parameters, ``pattern, ``lambda_prefix] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved cutoff prefix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "cutoff_prefix") proof
        setGoals [next]
      catch _ => saved.restore

open Lean Meta Elab Tactic in
elab "collect_actual_sibling_cutoff" : tactic => withMainContext do
  let mut inputProof : Lean.Expr := default
  let mut parent : Lean.Expr := default
  for decl in ← getLCtx do
    if decl.type.isAppOfArity ``CallIndex.Inputs 1 then
      inputProof := decl.toExpr
      parent := decl.type.appArg!
      break
  if parent == default then throwError "actual parent inputs missing"
  let constructors := (← getConstInfoInduct ``ChildStep).ctors
  for constructor in constructors do
    let saved ← saveState
    try
      let child ← mkFreshExprMVar (mkConst ``CallIndex)
      let target := mkApp2 (mkConst ``ChildStep) parent child
      let proof ← mkFreshExprMVar target
      let goals ← proof.mvarId!.apply (mkConst constructor)
      for goal in goals do
        unless ← goal.isAssigned do goal.assumption
      let proof ← instantiateMVars proof
      if proof.hasExprMVar then throwError "unresolved actual sibling"
      let belowType ← mkAppM ``State.LocalBindersBelowNextLocal #[← mkAppM ``CallIndex.initial #[parent]]
      let directType ← mkAppM ``State.DirectRequirementsAllocated #[← mkAppM ``CallIndex.initial #[parent]]
      let some below ← findLocalDeclWithType? belowType | throwError "local binder bound missing"
      let some direct ← findLocalDeclWithType? directType | throwError "direct allocation missing"
      let transition ← mkAppM ``child_transition #[inputProof, mkFVar below, mkFVar direct, proof]
      let (_, next) ← (← getMainGoal).note (Name.mkSimple "sibling_cutoff") transition
      setGoals [next]
    catch _ => saved.restore
end LocalReadCutoff

theorem ChildStep.read_cutoff {parent child : CallIndex} (inputs : parent.Inputs)
    (below : parent.initial.LocalBindersBelowNextLocal)
    (allocated : parent.initial.DirectRequirementsAllocated)
    (previous : LocalReadCutoff parent.initial) (step : ChildStep parent child) :
    LocalReadCutoff child.initial := by
  cases step
  case assignedValue_value accepted targetAccepted fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_actual_sibling_cutoff
    all_goals collect_cutoff_prefix
    all_goals simp only [CallIndex.initial, CallIndex.final] at *
    all_goals solve_by_elim (maxDepth := 10) (transparency := .reducible)
      [LocalReadCutoff.restore]
  case constructorApplication_arguments accepted arity fitting child =>
    split at fitting
    all_goals try cases Except.ok.inj fitting
    all_goals collect_actual_sibling_cutoff
    all_goals collect_cutoff_prefix
    all_goals simp only [CallIndex.initial, CallIndex.final] at *
    all_goals solve_by_elim (maxDepth := 10) (transparency := .reducible)
      [LocalReadCutoff.restore]
  all_goals collect_actual_sibling_cutoff
  all_goals collect_cutoff_prefix
  all_goals simp only [CallIndex.initial, CallIndex.final] at *
  all_goals try solve_by_elim (maxDepth := 10) (transparency := .reducible)
    [LocalReadCutoff.restore]
  case statement_match_cases =>
    have scrutinee := LocalReadCutoff.match_prefix inputs below allocated previous
      (by assumption) (by assumption) (by assumption) (by assumption)
    solve_by_elim (maxDepth := 5) (transparency := .reducible)
  case statement_match_default =>
    have scrutinee := LocalReadCutoff.match_prefix inputs below allocated previous
      (by assumption) (by assumption) (by assumption) (by assumption)
    solve_by_elim (maxDepth := 5) (transparency := .reducible)

theorem CallOccurrence.read_cutoff {root call : CallIndex} (inputs : root.Inputs)
    (below : root.initial.LocalBindersBelowNextLocal)
    (allocated : root.initial.DirectRequirementsAllocated)
    (previous : LocalReadCutoff root.initial) (here : CallOccurrence root call) :
    LocalReadCutoff call.initial := by
  induction here with
  | root _ => exact previous
  | child path step ih =>
    exact step.read_cutoff (path.inputs inputs)
      (ActualLocalAllocator.occurrence_bound inputs below path)
      (path.direct_prefix.allocated inputs.wellFormed allocated) ih

end Solcore.SourceSemantics.SourceInferenceExecution
