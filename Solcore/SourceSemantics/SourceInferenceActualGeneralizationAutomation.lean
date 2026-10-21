import Lean
import Solcore.SourceSemantics.SourceInferenceActualGeneralizationProgress

/-! Collect only kernel-checkable child-path evidence whose exact original
prefix equations are already present in the proof context. Failed constructor
matches are rolled back before another branch is considered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail

open Lean Meta Elab Tactic in
elab "actual_collect " parent:term : tactic => withMainContext do
  let parentProof ← elabTerm parent none
  let parentType ← whnf (← inferType parentProof)
  let parentCall := parentType.getAppArgs[1]!
  let info ← getConstInfoInduct ``ChildStep
  for ctor in info.ctors do
    let saved ← saveState
    try
      withoutRecover do
        let goal ← getMainGoal
        let child ← mkFreshExprMVar (mkConst ``CallIndex)
        let stepType ← mkAppM ``ChildStep #[parentCall, child]
        let step ← mkFreshExprMVar stepType
        let pending ← step.mvarId!.apply (mkConst ctor)
        setGoals pending
        evalTactic (← `(tactic| all_goals (first | assumption | rfl | exact AnnotationExpected.absent | (apply AnnotationExpected.present; assumption))))
        unless (← getUnsolvedGoals).isEmpty do throwError "Unproved actual prefix"
        let proof ← mkAppM ``CallOccurrence.child #[parentProof, ← instantiateMVars step]
        let proof ← instantiateMVars proof
        if proof.hasExprMVar then throwError "Unresolved actual prefix"
        let (_, next) ← goal.note (Name.mkSimple ("actual_" ++ ctor.getString!)) proof
        setGoals [next]
    catch _ => saved.restore


/- Instantiate an induction hypothesis only after matching its actual-call
premise to an already established child path. The remaining premises must be
existing equations or reflexive equalities. -/
open Lean Meta Elab Tactic in
elab "actual_invoke" : tactic => withMainContext do
  let locals := (← getLCtx).decls.toArray.filterMap id
  for hypothesis in locals do
    for reached in locals do
      let saved ← saveState
      try
        withoutRecover do
          let reachedType ← whnf reached.type
          unless reachedType.isAppOf ``CallOccurrence do throwError "Not an actual path"
          let (arguments, _, resultType) ← forallMetaTelescopeReducing hypothesis.type
          let resultType ← whnf resultType
          unless resultType.isAppOf ``ProgressFields do throwError "Not a progress hypothesis"
          let mut matched := false
          for argument in arguments do
            let type ← whnf (← inferType argument)
            if type.isAppOf ``CallOccurrence then
              unless ← isDefEq type reachedType do throwError "Different actual path"
              argument.mvarId!.assign reached.toExpr
              matched := true
          unless matched do throwError "No actual path premise"
          for argument in arguments do
            unless ← argument.mvarId!.isAssigned do
              let type ← instantiateMVars (← inferType argument)
              if ← isProp type then
                try argument.mvarId!.assumption catch _ => argument.mvarId!.refl
          let proof ← instantiateMVars (mkAppN hypothesis.toExpr arguments)
          if proof.hasExprMVar then throwError "Undetermined induction inputs"
          let goal ← getMainGoal
          let (_, next) ← goal.note `actual_progress proof
          setGoals [next]
      catch _ => saved.restore

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
