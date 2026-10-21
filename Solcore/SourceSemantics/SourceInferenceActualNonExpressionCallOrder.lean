import Lean
import Solcore.SourceSemantics.SourceInferenceActualCallOrder

/-! Actual non-expression siblings are identical or ordered by the allocator. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

private theorem fresh_order {before after : State} {type : Ty}
    (accepted : before.fresh = (type, after)) :
    before.inference.next ≤ after.inference.next := by
  have same := congrArg (fun result : Ty × State => result.2.inference.next) accepted
  simp only [State.fresh, InferState.fresh] at same
  omega

private theorem hidden_next {before after : State} {id : Resolved.LocalId}
    (accepted : before.allocateHiddenLocal = (id, after)) :
    after.inference.next = before.inference.next := by
  have same := congrArg (fun result : Resolved.LocalId × State => result.2.inference.next) accepted
  simpa only [State.allocateHiddenLocal] using same.symm

private theorem match_single_next {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {source : Syntax.Expr} {initial final terminal : State}
    {value result : InferredExpression}
    (accepted : matchScrutinee fuel context span [source] initial = .ok (result, terminal))
    (child : inferExprFuel fuel context source none initial = .ok (value, final)) :
    terminal.inference.next = final.inference.next := by
  simp only [matchScrutinee, child, Except.ok.injEq, Prod.mk.injEq] at accepted
  exact congrArg (fun s : State => s.inference.next) accepted.2.symm

private theorem match_many_next {fuel : Nat} {context : SourceInference.Context}
    {span : Syntax.SourceSpan} {sources : List Syntax.Expr} {initial final terminal : State}
    {values : List InferredExpression} {result : InferredExpression}
    (multiple : ∀ source, sources ≠ [source])
    (accepted : matchScrutinee fuel context span sources initial = .ok (result, terminal))
    (child : inferExprsFuel fuel context sources initial = .ok (values, final)) :
    terminal.inference.next = final.inference.next := by
  unfold matchScrutinee at accepted
  split at accepted
  next => grind
  next other =>
    simp only [child, bind, Except.bind, pure, Pure.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at accepted
    have same := congrArg (fun s : State => s.inference.next) accepted.2.symm
    change terminal.inference.next = final.inference.next at same
    exact same

open Lean Meta Elab Tactic in
elab "collect_allocator_order" : tactic => withMainContext do
  let hypotheses := (← getLCtx).getFVarIds
  for theoremName in [``unify_next, ``fresh_order, ``hidden_next] do
    for hypothesis in hypotheses do
      let saved ← saveState
      try
        let proof ← mkAppM theoremName #[mkFVar hypothesis]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved prefix"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "allocator_order") proof
        setGoals [next]
      catch _ => saved.restore
  for accepted in hypotheses do
    let type ← inferType (mkFVar accepted)
    unless type.isAppOf ``Eq do continue
    unless type.getAppArgs[1]!.isAppOf ``matchScrutinee do continue
    for child in hypotheses do
      let type ← inferType (mkFVar child)
      unless type.isAppOf ``Eq do continue
      unless type.getAppArgs[1]!.isAppOf ``inferExprFuel ||
          type.getAppArgs[1]!.isAppOf ``inferExprsFuel do continue
      let saved ← saveState
      try
        let proof ← mkAppM ``match_single_next #[mkFVar accepted, mkFVar child]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "unresolved singleton"
        let (_, next) ← (← getMainGoal).note (Name.mkSimple "scrutinee_order") proof
        setGoals [next]
      catch _ => saved.restore
      for multiple in hypotheses do
        let saved ← saveState
        try
          let proof ← mkAppM ``match_many_next #[mkFVar multiple, mkFVar accepted, mkFVar child]
          let proof ← instantiateMVars proof
          if proof.hasExprMVar then throwError "unresolved tuple"
          let (_, next) ← (← getMainGoal).note (Name.mkSimple "scrutinee_order") proof
          setGoals [next]
        catch _ => saved.restore

open Lean Meta Elab Tactic in
elab "collect_child_order " inputs:term : tactic => withMainContext do
  let inputsProof ← elabTerm inputs none
  let inputsType ← whnf (← inferType inputsProof)
  let parentCall := inputsType.getAppArgs[0]!
  let info ← getConstInfoInduct ``ChildStep
  for ctor in info.ctors do
    unless ctor.getString!.startsWith (parentCall.getAppFn.constName!.getString! ++ "_") do continue
    let saved ← saveState
    try
      withoutRecover do
        let goal ← getMainGoal
        let child ← mkFreshExprMVar (mkConst ``CallIndex)
        let stepType ← mkAppM ``ChildStep #[parentCall, child]
        let step ← mkFreshExprMVar stepType
        let pending ← step.mvarId!.apply (mkConst ctor)
        setGoals pending
        evalTactic (← `(tactic| all_goals (first | assumption | rfl)))
        unless (← getUnsolvedGoals).isEmpty do throwError "Unproved actual child prefix"
        let step ← instantiateMVars step
        let ready ← mkAppM ``ChildStep.inputs #[inputsProof, step]
        let accepted ← mkAppM ``ChildStep.child_accepted #[step]
        let progress ← mkAppM ``CallIndex.Inputs.progress #[ready, accepted]
        let progress ← mkAppM ``And.left #[progress]
        let order ← mkAppM ``State.InferenceProgress.next_le #[progress]
        let proof ← instantiateMVars order
        if proof.hasExprMVar then throwError "Unresolved actual child prefix"
        let (_, next) ← goal.note (Name.mkSimple ("order_" ++ ctor.getString!)) proof
        setGoals [next]
    catch _ => saved.restore


theorem ChildStep.constructorApplication_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {source : Syntax.Expr}
    {id : ExpressionId}
    {instantiation : DataConstructorInstantiation}
    {arguments : List Syntax.Expr}
    {expected : Option Ty}
    {initial : State}
    {value : InferredExpression}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.constructorApplication fuel context source id instantiation arguments expected initial value final).Inputs)
    (leftStep : ChildStep (CallIndex.constructorApplication fuel context source id instantiation arguments expected initial value final) left)
    (rightStep : ChildStep (CallIndex.constructorApplication fuel context source id instantiation arguments expected initial value final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.constructorArguments_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {sources : List Syntax.Expr}
    {expectedTypes : List Ty}
    {initial : State}
    {values : List InferredExpression}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.constructorArguments fuel context sources expectedTypes initial values final).Inputs)
    (leftStep : ChildStep (CallIndex.constructorArguments fuel context sources expectedTypes initial values final) left)
    (rightStep : ChildStep (CallIndex.constructorArguments fuel context sources expectedTypes initial values final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.statements_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {sources : List Syntax.Statement}
    {expectedReturn : Ty}
    {initial : State}
    {result : BlockResult}
    {left right : CallIndex}
    (inputs : (CallIndex.statements fuel context sources expectedReturn initial result).Inputs)
    (leftStep : ChildStep (CallIndex.statements fuel context sources expectedReturn initial result) left)
    (rightStep : ChildStep (CallIndex.statements fuel context sources expectedReturn initial result) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.statement_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {source : Syntax.Statement}
    {expectedReturn : Ty}
    {initial : State}
    {result : StatementResult}
    {left right : CallIndex}
    (inputs : (CallIndex.statement fuel context source expectedReturn initial result).Inputs)
    (leftStep : ChildStep (CallIndex.statement fuel context source expectedReturn initial result) left)
    (rightStep : ChildStep (CallIndex.statement fuel context source expectedReturn initial result) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.forItems_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {sources : List Syntax.ForItem}
    {initial : State}
    {result : InferredForItems}
    {left right : CallIndex}
    (inputs : (CallIndex.forItems fuel context sources initial result).Inputs)
    (leftStep : ChildStep (CallIndex.forItems fuel context sources initial result) left)
    (rightStep : ChildStep (CallIndex.forItems fuel context sources initial result) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.forItem_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {source : Syntax.ForItem}
    {initial : State}
    {value : ForItemForm}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.forItem fuel context source initial value final).Inputs)
    (leftStep : ChildStep (CallIndex.forItem fuel context source initial value final) left)
    (rightStep : ChildStep (CallIndex.forItem fuel context source initial value final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.place_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {source : Syntax.Expr}
    {initial : State}
    {value : PlaceResolution}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.place fuel context source initial value final).Inputs)
    (leftStep : ChildStep (CallIndex.place fuel context source initial value final) left)
    (rightStep : ChildStep (CallIndex.place fuel context source initial value final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.assignedValue_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {target : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {value : Syntax.Expr}
    {initial : State}
    {assignment : AssignmentResolution}
    {inferred : InferredExpression}
    {final : State}
    {left right : CallIndex}
    (inputs : (CallIndex.assignedValue fuel context target operator value initial assignment inferred final).Inputs)
    (leftStep : ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) left)
    (rightStep : ChildStep (CallIndex.assignedValue fuel context target operator value initial assignment inferred final) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals cases operator <;> simp_all only [pure, Pure.pure, Except.pure]
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


theorem ChildStep.matchCases_ordered
    {fuel : Nat}
    {context : SourceInference.Context}
    {scrutineeType expectedReturn : Ty}
    {saved : LexicalScope}
    {cases : List Syntax.MatchCase}
    {initial : State}
    {result : MatchCasesResult}
    {left right : CallIndex}
    (inputs : (CallIndex.matchCases fuel context scrutineeType expectedReturn saved cases initial result).Inputs)
    (leftStep : ChildStep (CallIndex.matchCases fuel context scrutineeType expectedReturn saved cases initial result) left)
    (rightStep : ChildStep (CallIndex.matchCases fuel context scrutineeType expectedReturn saved cases initial result) right) : left.Ordered right := by
  have leftProgress := ((leftStep.inputs inputs).progress leftStep.child_accepted).1.next_le
  have rightProgress := ((rightStep.inputs inputs).progress rightStep.child_accepted).1.next_le
  cases leftStep
  all_goals collect_child_order inputs
  all_goals cases rightStep
  all_goals collect_child_order inputs
  all_goals simp_all [CallIndex.Ordered, CallIndex.Accepted, CallIndex.initial, CallIndex.final]
  all_goals collect_child_order inputs
  all_goals collect_allocator_order
  all_goals try simp only [State.restoreLexicalScope] at *
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega
  all_goals try solve | grind [AnnotationExpected]
  all_goals try dsimp only [CallIndex.initial, CallIndex.final, State.restoreLexicalScope] at *
  all_goals try omega


end Solcore.SourceSemantics.SourceInferenceExecution
