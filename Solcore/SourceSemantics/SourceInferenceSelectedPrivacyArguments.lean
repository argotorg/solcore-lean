import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyReferences

/-! Privacy follows the exact argument-fitting trace and its real intermediate
states. Each committed expected-type fit contributes its actual new rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem new_requirements_trans {protectedVars : List TypeVarId} {before middle after : State}
    (first : ∀ row ∈ middle.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars middle row.predicate)
    (second : ∀ row ∈ after.requirements, row ∉ middle.requirements →
      PredicateSafe protectedVars after row.predicate)
    (transport : SafeTransport protectedVars middle after) :
    ∀ row ∈ after.requirements, row ∉ before.requirements →
      PredicateSafe protectedVars after row.predicate := by
  intro row member fresh
  by_cases old : row ∈ middle.requirements
  · intro type typeMember
    exact transport type (first row old fresh type typeMember)
  · exact second row member old

private theorem candidate_fit {context : SourceInference.Context} {state : State}
    {actual : InferredExpression} {expected : Option Ty} {result : Detail.ExpectationResult}
    (accepted : Detail.candidateWithExpected context state actual expected = .ok (some result)) :
    Detail.withExpected context state actual expected = .ok result := by
  unfold Detail.candidateWithExpected at accepted
  cases fitted : Detail.withExpected context state actual expected with
  | ok value =>
    simp only [fitted, Except.ok.injEq, Option.some.injEq] at accepted
    cases accepted
    rfl
  | error error =>
    cases error <;> simp [fitted] at accepted
    all_goals cases ‹Unification.Error› <;> simp_all

private theorem fitTrace_private {protectedVars : List TypeVarId} {context : SourceInference.Context}
    (catalog : SignatureCatalogWellFormed context.signatures)
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (trace : Detail.ArgumentFitTrace context state arguments parameters result) :
    state.InferenceReady →
    (∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next) →
    (∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next) →
    (∀ argument ∈ arguments, Safe protectedVars state argument.type) →
    (∀ parameter ∈ parameters, Safe protectedVars state parameter) →
    LiveBindersSafe protectedVars state →
    SafeTransport protectedVars state result.state ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate := by
  induction trace with
  | nil state =>
    intro _ _ _ _ _ live
    exact ⟨.refl _ _, live, fun _ member fresh => (fresh member).elim⟩
  | @cons state argument arguments parameter parameters fitted tail head rest ih =>
    intro ready argumentsBelow parametersBelow argumentsSafe parametersSafe live
    have accepted := candidate_fit head
    have argumentBelow := argumentsBelow argument (by simp)
    have parameterBelow := parametersBelow parameter (by simp)
    have expectedBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact parameterBelow
    have expectedSafe : ∀ type ∈ some parameter, Safe protectedVars state type := by
      intro type member
      cases Option.mem_def.mp member
      exact parametersSafe parameter (by simp)
    have fitProgress := Detail.withExpected_inferenceProperties ready argumentBelow expectedBelow accepted
    have fitting := withExpected_private ready argumentBelow expectedBelow
      (argumentsSafe argument (by simp)) expectedSafe live accepted
    have issued := withExpected_new_requirements_private catalog ready
      (argumentsSafe argument (by simp)) expectedSafe accepted
    have later := ih fitProgress.2.1
      (fun arg member => (argumentsBelow arg (List.mem_cons_of_mem _ member)).weaken fitProgress.1.next_le)
      (fun param member => (parametersBelow param (List.mem_cons_of_mem _ member)).weaken fitProgress.1.next_le)
      (fun arg member => fitting.1 _ (argumentsSafe arg (List.mem_cons_of_mem _ member)))
      (fun param member => fitting.1 _ (parametersSafe param (List.mem_cons_of_mem _ member)))
      fitting.2.2
    exact ⟨fitting.1.trans later.1, later.2.1,
      new_requirements_trans issued later.2.2 later.1⟩

/-- The accepted executable argument pass supplies the entire ordered trace;
no argument-fitting law is assumed by callers. -/
theorem fitArguments_private {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (catalog : SignatureCatalogWellFormed context.signatures)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (parametersSafe : ∀ parameter ∈ parameters, Safe protectedVars state parameter)
    (live : LiveBindersSafe protectedVars state)
    (accepted : Detail.fitArguments context state arguments parameters = .ok (some result)) :
    SafeTransport protectedVars state result.state ∧
    LiveBindersSafe protectedVars result.state ∧
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateSafe protectedVars result.state row.predicate :=
  fitTrace_private catalog (Detail.fitArguments_some_trace accepted) ready
    argumentsBelow parametersBelow argumentsSafe parametersSafe live

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
