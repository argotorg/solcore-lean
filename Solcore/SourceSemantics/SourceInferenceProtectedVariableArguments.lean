import Solcore.SourceSemantics.SourceInferenceProtectedVariableFrameContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
open Frontend SourceInference TypeSystem

theorem recordExpressionWithExpected_fixes_protected
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {start : Option Nat} {result : InferredExpression × State}
    (fixed : FixesProtected protectedVars state)
    (typeSafe : Safe protectedVars state type)
    (expectedSafe : ∀ type ∈ expected, Safe protectedVars state type)
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements
      expected state start = .ok result) :
    FixesProtected protectedVars result.2 := by
  unfold Detail.recordExpressionWithExpected at accepted
  cases fitted : Detail.withExpected context state {id, type} expected with
  | error error => simp [fitted, bind, Except.bind] at accepted
  | ok fit =>
    simp only [fitted, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact (withExpected_fixes_protected fixed typeSafe expectedSafe fitted).of_substitution_eq rfl

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

private theorem fitTrace_fixes_protected
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (trace : Detail.ArgumentFitTrace context state arguments parameters result) :
    state.InferenceReady →
    (∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next) →
    (∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next) →
    (∀ argument ∈ arguments, Safe protectedVars state argument.type) →
    (∀ parameter ∈ parameters, Safe protectedVars state parameter) →
    LiveBindersSafe protectedVars state →
    FixesProtected protectedVars state →
    FixesProtected protectedVars result.state := by
  induction trace with
  | nil state =>
    intro _ _ _ _ _ _ fixed
    exact fixed
  | @cons state argument arguments parameter parameters fitted tail head rest ih =>
    intro ready argumentsBelow parametersBelow argumentsSafe parametersSafe live fixed
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
    have fittedFixed := withExpected_fixes_protected fixed (argumentsSafe argument (by simp)) expectedSafe accepted
    exact ih fitProgress.2.1
      (fun arg member => (argumentsBelow arg (List.mem_cons_of_mem _ member)).weaken fitProgress.1.next_le)
      (fun param member => (parametersBelow param (List.mem_cons_of_mem _ member)).weaken fitProgress.1.next_le)
      (fun arg member => fitting.1 _ (argumentsSafe arg (List.mem_cons_of_mem _ member)))
      (fun param member => fitting.1 _ (parametersSafe param (List.mem_cons_of_mem _ member)))
      fitting.2.2 fittedFixed

theorem fitArguments_fixes_protected
    {protectedVars : List TypeVarId} {context : SourceInference.Context}
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next)
    (argumentsSafe : ∀ argument ∈ arguments, Safe protectedVars state argument.type)
    (parametersSafe : ∀ parameter ∈ parameters, Safe protectedVars state parameter)
    (live : LiveBindersSafe protectedVars state)
    (fixed : FixesProtected protectedVars state)
    (accepted : Detail.fitArguments context state arguments parameters = .ok (some result)) :
    FixesProtected protectedVars result.state :=
  fitTrace_fixes_protected (Detail.fitArguments_some_trace accepted) ready
    argumentsBelow parametersBelow argumentsSafe parametersSafe live fixed

end Solcore.SourceSemantics.SourceInferenceSoundness.ProtectedVariables
