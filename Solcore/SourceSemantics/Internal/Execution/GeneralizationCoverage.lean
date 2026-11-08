import Lean
import Solcore.SourceSemantics.Internal.Execution.Reads
import Solcore.SourceSemantics.Internal.Execution.CallGraph
import Solcore.SourceSemantics.Ownership

/-!
# Coverage of generalizations

The initialized-binding inventory is covered by exact origins.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualGeneralizationAutomation
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
          unless resultType.isAppOf ``ProgressFields || resultType.isAppOf ``RelativeReadProgressFields do throwError "Not a progress hypothesis"
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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceActualGeneralizationCoverage
/-! The executable initialized-binding inventory is covered by exact actual
statement and header origins, including every recorded loop header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem
variable {root : CallIndex}

private theorem Item.initialized {item : ForItemForm} (origin : Item root item)
    {binding : InitializedLetBinding} (member : binding ∈ forItemInitializedLetBindings item) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      Origin root binding.binder initializer := by
  cases item with
  | letDecl binder value =>
    cases value with
    | none => simp only [forItemInitializedLetBindings, List.not_mem_nil] at member
    | some initializer =>
      simp only [forItemInitializedLetBindings, List.mem_singleton] at member
      subst binding
      exact ⟨initializer, rfl, origin _ _ rfl⟩
  | expression _ | assignValue _ _ _ | assignBitNot _ =>
    simp only [forItemInitializedLetBindings, List.not_mem_nil] at member

private theorem Items.initialized {items : List ForItemForm} (origins : Items root items)
    {binding : InitializedLetBinding} (member : binding ∈ items.flatMap forItemInitializedLetBindings) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      Origin root binding.binder initializer := by
  obtain ⟨item, present, member⟩ := List.mem_flatMap.mp member
  exact (origins item present).initialized member

private theorem Statement.initialized {node : StatementNode} (origin : Statement root node)
    {binding : InitializedLetBinding} (member : binding ∈ statementInitializedLetBindings node.form) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      Origin root binding.binder initializer := by
  cases form : node.form with
  | letDecl binder value =>
    cases value with
    | none => simp only [form, statementInitializedLetBindings, List.not_mem_nil] at member
    | some initializer =>
      simp only [form, statementInitializedLetBindings, List.mem_singleton] at member
      subst binding
      exact ⟨initializer, rfl, by simpa only [Statement, form] using origin⟩
  | forLoop initial condition post body =>
    have events : Items root initial ∧ Items root post := by
      simpa only [Statement, form] using origin
    simp only [form, statementInitializedLetBindings, List.mem_append] at member
    rcases member with first | second
    · exact events.1.initialized first
    · exact events.2.initialized second
  | _ => simp only [form, statementInitializedLetBindings, List.not_mem_nil] at member


/-- Every executable initialized binding has an actual receipt on the same
inference root, with the complete binder and initializer identity preserved. -/
theorem Origins.initialized {source : TypedSource} (origins : Origins root source.nodes)
    {binding : InitializedLetBinding} (member : binding ∈ initializedLetBindings source) :
    ∃ initializer, binding.initializer = .expression initializer ∧
      Origin root binding.binder initializer := by
  obtain ⟨node, present, member⟩ := List.mem_flatMap.mp member
  cases node with
  | expression _ => cases member
  | statement node => exact (origins node present).initialized member

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
end
