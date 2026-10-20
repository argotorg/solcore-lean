import Solcore.SourceSemantics.SourceInferenceActualMatchCompletion
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeMatchCases
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps

/-! Events in actual match arms and defaults survive the remaining match suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail SourceInferenceExecution
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}

theorem match_after_cases
    {entryNext fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {state : State} {checked : MatchCasesResult} {result : StatementResult} {outputs : List Ty}
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnBefore : expectedReturn.VariablesBelow entryNext)
    (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state = .ok checked)
    (accepted : matchCompletion fuel context statement id hidden scrutinee arms expectedReturn state = .ok result)
    (lifetime : GeneralizationLifetime event entryNext checked.state outputs) :
    GeneralizationLifetime event entryNext result.state [result.type] := by
  have casesProperties := inferMatchCasesFuel_inferenceProperties ready catalog.formation catalog.canonical
    scrutineeBelow returnBelow rfl casesAccepted
  unfold matchCompletion at accepted
  simp only [casesAccepted, bind, Except.bind] at accepted
  cases defaultEq : arms.value.defaultBody with
  | none =>
      simp only [defaultEq, pure, Pure.pure, Except.pure] at accepted
      split at accepted
      · cases accepted
      · injection accepted with resultEq
        subst result
        refine (lifetime.recordNode _).replaceOutputs ?_
        intro type member
        cases List.mem_singleton.mp member
        split
        · exact (show Safe binder.scheme.quantified checked.state (checked.state.resolve expectedReturn) from safe_resolved casesProperties.2.1 (lifetime.older _ returnBefore))
        · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)
  | some body =>
      cases bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state with
      | error error => simp [defaultEq, bodyAccepted] at accepted
      | ok bodyResult =>
          have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1 catalog.formation catalog.canonical
            (returnBelow.weaken casesProperties.1.next_le) bodyAccepted
          have bodyLife := lifetime.inferStatements casesProperties.2.1
            ((inferMatchCasesFuel_direct_progress casesAccepted).wellFormed wellFormed) catalog
            (returnBelow.weaken casesProperties.1.next_le) (lifetime.older _ returnBefore) bodyAccepted
          have savedSubset : state.localBinders ⊆ bodyResult.state.localBinders := by
            have same : checked.state.localBinders = state.localBinders := congrArg LexicalScope.binders casesProperties.2.2
            rw [← same]
            exact inferStatementsFuel_binders_subset bodyAccepted
          have restored := bodyLife.restoreScope state.lexicalScope savedSubset
          have restoredReady := (State.restoreLexicalScope_inferenceProperties ready
            (casesProperties.1.trans bodyProperties.1)).2
          simp only [defaultEq, bodyAccepted, pure, Pure.pure, Except.pure] at accepted
          split at accepted
          · cases accepted
          · injection accepted with resultEq
            subst result
            refine (restored.recordNode _).replaceOutputs ?_
            intro type member
            cases List.mem_singleton.mp member
            split
            · exact (show Safe binder.scheme.quantified (bodyResult.state.restoreLexicalScope state.lexicalScope) ((bodyResult.state.restoreLexicalScope state.lexicalScope).resolve expectedReturn) from safe_resolved restoredReady (restored.older _ returnBefore))
            · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)

theorem match_after_default
    {fuel : Nat} {context : SourceInference.Context}
    {statement : Syntax.Statement} {id : StatementId} {hidden : Resolved.LocalId}
    {scrutinee : InferredExpression} {arms : Syntax.MatchArms} {expectedReturn : Ty}
    {state : State} {checked : MatchCasesResult} {body : Syntax.Block}
    {bodyResult : BlockResult} {result : StatementResult}
    (ready : state.InferenceReady) (catalog : LifetimeInferenceContext context)
    (scrutineeBelow : scrutinee.type.VariablesBelow state.inference.next)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (casesAccepted : inferMatchCasesFuel fuel context scrutinee.type expectedReturn state.lexicalScope arms.value.cases state = .ok checked)
    (defaultEq : arms.value.defaultBody = some body)
    (bodyAccepted : inferStatementsFuel fuel context body.value expectedReturn checked.state = .ok bodyResult)
    (accepted : matchCompletion fuel context statement id hidden scrutinee arms expectedReturn state = .ok result)
    (lifetime : GeneralizationLifetime event checked.state.inference.next bodyResult.state [bodyResult.type]) :
    GeneralizationLifetime event state.inference.next result.state [result.type] := by
  have casesProperties := inferMatchCasesFuel_inferenceProperties ready catalog.formation catalog.canonical
    scrutineeBelow returnBelow rfl casesAccepted
  have bodyProperties := inferStatementsFuel_inferenceProperties casesProperties.2.1 catalog.formation catalog.canonical
    (returnBelow.weaken casesProperties.1.next_le) bodyAccepted
  have savedSubset : state.localBinders ⊆ bodyResult.state.localBinders := by
    have same : checked.state.localBinders = state.localBinders := congrArg LexicalScope.binders casesProperties.2.2
    rw [← same]
    exact inferStatementsFuel_binders_subset bodyAccepted
  have restored := (lifetime.restoreScope state.lexicalScope savedSubset).weaken_entry casesProperties.1.next_le
  have restoredReady := (State.restoreLexicalScope_inferenceProperties ready
    (casesProperties.1.trans bodyProperties.1)).2
  unfold matchCompletion at accepted
  simp only [casesAccepted, defaultEq, bodyAccepted, bind, Except.bind, pure, Pure.pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · injection accepted with resultEq
    subst result
    refine (restored.recordNode _).replaceOutputs ?_
    intro type member
    cases List.mem_singleton.mp member
    split
    · exact (show Safe binder.scheme.quantified (bodyResult.state.restoreLexicalScope state.lexicalScope) ((bodyResult.state.restoreLexicalScope state.lexicalScope).resolve expectedReturn) from safe_resolved restoredReady (restored.older _ returnBelow))
    · exact safe_closed _ _ (Ty.variablesBelow_constructor _ _)

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
