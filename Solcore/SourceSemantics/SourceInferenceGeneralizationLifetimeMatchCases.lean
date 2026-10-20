import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeArgumentContinuation
import Solcore.SourceSemantics.SourceInferencePatternActiveOrigins

/-! Match-arm events follow the real pattern, scope restoration and remaining arms. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {fuel : Nat} {context : SourceInference.Context} {scrutinee expectedReturn : Ty}
    {saved : LexicalScope} {arm : Syntax.MatchCase} {rest : List Syntax.MatchCase}
    {initial patternState : State} {pattern : TypedMatchPattern} {body : BlockResult}
    {tail result : MatchCasesResult}

private theorem resultState
    (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutinee initial = .ok (pattern, patternState))
    (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
    (tailAccepted : inferMatchCasesFuel fuel context scrutinee expectedReturn saved rest
      (body.state.restoreLexicalScope saved) = .ok tail)
    (accepted : inferMatchCasesFuel (fuel + 1) context scrutinee expectedReturn saved (arm :: rest) initial = .ok result) :
    result.state = tail.state := by
  unfold inferMatchCasesFuel at accepted
  simp only [patternAccepted, bodyAccepted, tailAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
  exact (congrArg MatchCasesResult.state accepted).symm

theorem matchCases_body
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.VariablesBelow initial.inference.next)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (scope : initial.lexicalScope = saved)
    (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutinee initial = .ok (pattern, patternState))
    (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
    (tailAccepted : inferMatchCasesFuel fuel context scrutinee expectedReturn saved rest
      (body.state.restoreLexicalScope saved) = .ok tail)
    (accepted : inferMatchCasesFuel (fuel + 1) context scrutinee expectedReturn saved (arm :: rest) initial = .ok result)
    (lifetime : GeneralizationLifetime event patternState.inference.next body.state [body.type]) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  have patternProperties := inferMatchPatternFuel_inferenceProperties ready scrutineeBelow catalog.formation patternAccepted
  have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1 catalog.formation catalog.canonical
    (returnBelow.weaken patternProperties.1.next_le) bodyAccepted
  have throughBody := patternProperties.1.trans bodyProperties.1
  have restoredProperties := State.restoreLexicalScope_inferenceProperties ready throughBody
  have savedSubset : saved.binders ⊆ body.state.localBinders := by
    rw [← scope]
    exact (inferMatchPatternFuel_scope patternAccepted).retained.trans
      (inferStatementsFuel_binders_subset bodyAccepted)
  have restored := lifetime.restoreScope saved savedSubset
  have bodyWF := (inferStatementsFuel_direct_progress bodyAccepted).wellFormed
    ((inferMatchPatternFuel_direct_progress patternAccepted).wellFormed wellFormed)
  have after := restored.inferMatchCases
    (scope ▸ restoredProperties.2) bodyWF catalog
    (scrutineeBelow.weaken throughBody.next_le)
    (restored.older _ (scrutineeBelow.weaken patternProperties.1.next_le))
    (returnBelow.weaken throughBody.next_le)
    (restored.older _ (returnBelow.weaken patternProperties.1.next_le)) (by rfl) tailAccepted
  rw [resultState patternAccepted bodyAccepted tailAccepted accepted]
  exact (after.restrict_outputs (by simp)).weaken_entry patternProperties.1.next_le

theorem matchCases_tail
    (ready : initial.InferenceReady) (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.VariablesBelow initial.inference.next)
    (returnBelow : expectedReturn.VariablesBelow initial.inference.next)
    (_scope : initial.lexicalScope = saved)
    (patternAccepted : inferMatchPatternFuel fuel context arm.value.pattern scrutinee initial = .ok (pattern, patternState))
    (bodyAccepted : inferStatementsFuel fuel context arm.value.body.value expectedReturn patternState = .ok body)
    (tailAccepted : inferMatchCasesFuel fuel context scrutinee expectedReturn saved rest
      (body.state.restoreLexicalScope saved) = .ok tail)
    (accepted : inferMatchCasesFuel (fuel + 1) context scrutinee expectedReturn saved (arm :: rest) initial = .ok result)
    (lifetime : GeneralizationLifetime event body.state.inference.next tail.state []) :
    GeneralizationLifetime event initial.inference.next result.state [] := by
  have patternProperties := inferMatchPatternFuel_inferenceProperties ready scrutineeBelow catalog.formation patternAccepted
  have bodyProperties := inferStatementsFuel_inferenceProperties patternProperties.2.1 catalog.formation catalog.canonical
    (returnBelow.weaken patternProperties.1.next_le) bodyAccepted
  rw [resultState patternAccepted bodyAccepted tailAccepted accepted]
  exact lifetime.weaken_entry (patternProperties.1.trans bodyProperties.1).next_le

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
