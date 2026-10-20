import Solcore.SourceSemantics.SourceInferenceActualCallProperties

/-! The match scrutinee prefix retains the real scalar or synthetic tuple call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

theorem matchScrutinee_properties
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {result : InferredExpression × State}
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (accepted : matchScrutinee fuel context span sources initial = .ok result) :
    initial.InferenceProgress result.2 ∧ result.2.InferenceReady ∧
      result.1.type.VariablesBelow result.2.inference.next := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact inferExprFuel_inferenceProperties ready catalog.formation catalog.canonical (by simp) accepted
  · cases run : inferExprsFuel fuel context sources initial with
    | error error => simp [run, bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨values, state⟩ := pair
      simp only [run, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      have facts := inferExprsFuel_inferenceProperties ready catalog.formation catalog.canonical run
      have progress := facts.1.trans (State.InferenceProgress.allocateExpressionId state facts.2.1.solved)
      have allocatedReady := facts.2.1.allocateExpressionId
      refine ⟨progress.trans (.recordNode _ _ allocatedReady.solved), allocatedReady.recordNode _, ?_⟩
      apply Ty.variablesBelow_productMany
      intro type member
      obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
      exact facts.2.2 value present

theorem matchScrutinee_wellFormed
    {fuel : Nat} {context : SourceInference.Context} {span : Syntax.SourceSpan}
    {sources : List Syntax.Expr} {initial : State} {result : InferredExpression × State}
    (wellFormed : initial.RequirementsWellFormed)
    (accepted : matchScrutinee fuel context span sources initial = .ok result) :
    result.2.RequirementsWellFormed := by
  unfold matchScrutinee at accepted
  split at accepted
  · exact (inferExprFuel_direct_progress accepted).wellFormed wellFormed
  · cases run : inferExprsFuel fuel context sources initial with
    | error error => simp [run, bind, Except.bind] at accepted
    | ok pair =>
      obtain ⟨values, state⟩ := pair
      simp only [run, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
      cases accepted
      exact (inferExprsFuel_direct_progress run).wellFormed wellFormed

end Solcore.SourceSemantics.SourceInferenceExecution
