import Solcore.SourceSemantics.SourceInferenceNormalizedExpectedFormation

/-! Requirement formation along the actual ordered argument-fitting trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem

/-- Both batches are interpreted by one final substitution. Actual ledger
membership selects which accepted step issued a newly retained row. -/
theorem new_normalized_requirements_trans
    {semantic : SourceSemantics.Context} {outer : Substitution} {before middle after : State}
    (first : ∀ row ∈ middle.requirements, row ∉ before.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate))
    (second : ∀ row ∈ after.requirements, row ∉ middle.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate)) :
    ∀ row ∈ after.requirements, row ∉ before.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  intro row member fresh
  by_cases previous : row ∈ middle.requirements
  · exact first row previous fresh
  · exact second row member previous

/-- Continuation to the selected finalizer is recovered at each actual fit
from the remaining accepted argument trace and its inference progress. -/
theorem argumentFitTrace_normalized_issuance
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (trace : Detail.ArgumentFitTrace context state arguments parameters result) :
    state.InferenceReady →
    (∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next) →
    (∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next) →
    (∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type)) →
    (∀ parameter ∈ parameters, TypeAdmissible semantic (outer.apply parameter)) →
    outer.SemanticallyExtends result.state.inference.substitution →
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  induction trace with
  | nil state =>
    exact fun _ _ _ _ _ _ _ member fresh => (fresh member).elim
  | @cons state argument arguments parameter parameters fitted tail head rest ih =>
    intro ready argumentsBelow parametersBelow argumentsFormed parametersFormed continuation
    have expectedBelow : ∀ type ∈ some parameter, type.VariablesBelow state.inference.next := by
      intro type member
      cases Option.mem_def.mp member
      exact parametersBelow parameter (by simp)
    have fittedProperties := Detail.candidateWithExpected_some_inferenceProperties ready
      (argumentsBelow argument (by simp)) expectedBelow head
    have tailArgumentsBelow : ∀ arg ∈ arguments, arg.type.VariablesBelow fitted.state.inference.next := by
      intro arg member
      exact (argumentsBelow arg (List.mem_cons_of_mem _ member)).weaken fittedProperties.1.next_le
    have tailParametersBelow : ∀ type ∈ parameters, type.VariablesBelow fitted.state.inference.next := by
      intro type member
      exact (parametersBelow type (List.mem_cons_of_mem _ member)).weaken fittedProperties.1.next_le
    have tailProperties := rest.inferenceProperties fittedProperties.2.1 tailArgumentsBelow tailParametersBelow
    have fittedContinuation : outer.SemanticallyExtends fitted.state.inference.substitution :=
      continuation.trans tailProperties.1.substitution_extends
    have expectedFormed : ∀ type ∈ some parameter, TypeAdmissible semantic (outer.apply type) := by
      intro type member
      cases Option.mem_def.mp member
      exact parametersFormed parameter (by simp)
    have headFormation := candidateWithExpected_normalized_formation formation fittedContinuation
      (argumentsFormed argument (by simp)) expectedFormed head
    have tailFormation := ih fittedProperties.2.1 tailArgumentsBelow tailParametersBelow
      (fun arg member => argumentsFormed arg (List.mem_cons_of_mem _ member))
      (fun type member => parametersFormed type (List.mem_cons_of_mem _ member)) continuation
    exact new_normalized_requirements_trans headFormation.2 tailFormation

/-- The executable argument pass supplies the trace used above. -/
theorem fitArguments_normalized_issuance
    {semantic : SourceSemantics.Context} {context : SourceInference.Context} {outer : Substitution}
    {state : State} {arguments : List InferredExpression} {parameters : List Ty}
    {result : Detail.ArgumentFitResult}
    (formation : FormationContext semantic context outer)
    (ready : state.InferenceReady)
    (argumentsBelow : ∀ argument ∈ arguments, argument.type.VariablesBelow state.inference.next)
    (parametersBelow : ∀ parameter ∈ parameters, parameter.VariablesBelow state.inference.next)
    (argumentsFormed : ∀ argument ∈ arguments, TypeAdmissible semantic (outer.apply argument.type))
    (parametersFormed : ∀ parameter ∈ parameters, TypeAdmissible semantic (outer.apply parameter))
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.fitArguments context state arguments parameters = .ok (some result)) :
    ∀ row ∈ result.state.requirements, row ∉ state.requirements →
      PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) :=
  argumentFitTrace_normalized_issuance formation (Detail.fitArguments_some_trace accepted)
    ready argumentsBelow parametersBelow argumentsFormed parametersFormed continuation

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
