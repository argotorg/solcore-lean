import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeStateSteps

/-! Actual argument and match suffix inference for events already created. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem Detail
namespace GeneralizationLifetime
variable {whole : TypedSource} {finalSubstitution : Substitution}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization whole finalSubstitution binder initializer}
    {entryNext : Nat} {state : State} {outputs : List Ty}
    {fuel : Nat} {context : SourceInference.Context}

theorem inferConstructorArguments
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {sources : List Syntax.Expr} {expectedTypes : List Ty} {result : List InferredExpression × State}
    (expectedBelow : ∀ type ∈ expectedTypes, type.VariablesBelow state.inference.next)
    (expectedSafe : ∀ type ∈ expectedTypes, Safe binder.scheme.quantified state type)
    (accepted : inferConstructorArgumentsFuel fuel context sources expectedTypes state = .ok result) :
    GeneralizationLifetime event entryNext result.2 (outputs ++ result.1.map (·.type)) := by
  have privacy := inferConstructorArgumentsFuel_private binder.scheme.quantified fuel context sources expectedTypes state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    expectedBelow expectedSafe result accepted
  have progress := inferConstructorArgumentsFuel_inferenceProperties ready catalog.formation catalog.canonical
    expectedBelow accepted
  refine lifetime.append progress.1.next_le privacy.1 privacy.2.2.1 ?_ privacy.2.2.2
  intro type member
  obtain ⟨expression, present, rfl⟩ := List.mem_map.mp member
  exact privacy.2.1 expression present

theorem inferMatchCases
    (lifetime : GeneralizationLifetime event entryNext state outputs)
    (ready : state.InferenceReady) (wellFormed : state.RequirementsWellFormed)
    (catalog : LifetimeInferenceContext context)
    {scrutinee expectedReturn : Ty} {saved : LexicalScope}
    {cases : List Syntax.MatchCase} {result : MatchCasesResult}
    (scrutineeBelow : scrutinee.VariablesBelow state.inference.next)
    (scrutineeSafe : Safe binder.scheme.quantified state scrutinee)
    (returnBelow : expectedReturn.VariablesBelow state.inference.next)
    (returnSafe : Safe binder.scheme.quantified state expectedReturn)
    (scope : state.lexicalScope = saved)
    (accepted : inferMatchCasesFuel fuel context scrutinee expectedReturn saved cases state = .ok result) :
    GeneralizationLifetime event entryNext result.state outputs := by
  have privacy := inferMatchCasesFuel_private binder.scheme.quantified fuel context scrutinee expectedReturn saved cases state
    ready wellFormed lifetime.bound lifetime.live catalog.catalog catalog.formation catalog.canonical
    scrutineeBelow scrutineeSafe returnBelow returnSafe scope result accepted
  have progress := inferMatchCasesFuel_inferenceProperties ready catalog.formation catalog.canonical
    scrutineeBelow returnBelow scope accepted
  simpa only [List.append_nil] using lifetime.append (newOutputs := [])
    progress.1.next_le privacy.1 privacy.2.1 (by simp) privacy.2.2

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
