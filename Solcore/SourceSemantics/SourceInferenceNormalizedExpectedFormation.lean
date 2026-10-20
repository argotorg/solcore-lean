import Solcore.SourceSemantics.SourceInferenceNormalizedOperatorIssuance

/-! Actual expected fitting and its recording wrapper form their result and
new obligations under the selected final continuation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
open Frontend SourceInference TypeSystem SourceInferenceRequirementFormation

theorem withExpected_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (actualFormed : TypeAdmissible semantic (outer.apply actual.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.withExpected context state actual expected = .ok result) :
    TypeAdmissible semantic (outer.apply result.expression.type) ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  rcases Detail.withExpected_success_cases accepted with simple | coerced
  · refine ⟨?_, ?_⟩
    · rw [← simple.2.2]
      exact (continuation actual.type).symm ▸ actualFormed
    · intro row member fresh
      exact (fresh (simple.2.1 ▸ member)).elim
  · obtain ⟨expectedType, plan, expectedEq, planned, resultEq⟩ := coerced
    subst result
    have extension : outer.SemanticallyExtends state.inference.substitution := by
      intro type
      have eq := continuation type
      change outer.apply ((Detail.commitCoercionPlan state plan).2.resolve type) =
        outer.apply type at eq
      rw [Detail.commitCoercionPlan_resolve] at eq
      exact eq
    have target := expectedFormed expectedType (by simp [expectedEq])
    refine ⟨(extension expectedType).symm ▸ target, ?_⟩
    exact withExpected_new_requirements_formation formation extension actualFormed expectedFormed accepted

theorem candidateWithExpected_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {state : State} {actual : InferredExpression} {expected : Option Ty}
    {result : Detail.ExpectationResult} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.state.inference.substitution)
    (actualFormed : TypeAdmissible semantic (outer.apply actual.type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.candidateWithExpected context state actual expected = .ok (some result)) :
    TypeAdmissible semantic (outer.apply result.expression.type) ∧
      ∀ row ∈ result.state.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  exact withExpected_normalized_formation formation continuation actualFormed expectedFormed
    (Detail.candidateWithExpected_some_withExpected accepted)

theorem recordExpressionWithExpected_normalized_formation
    {semantic : SourceSemantics.Context} {context : SourceInference.Context}
    {source : Syntax.Expr} {id : ExpressionId} {type : Ty} {form : ExpressionForm}
    {requirements : List RequirementId} {expected : Option Ty} {state : State}
    {localSchemeInstantiationStart : Option Nat} {result : InferredExpression × State} {outer : Substitution}
    (formation : FormationContext semantic context outer)
    (continuation : outer.SemanticallyExtends result.2.inference.substitution)
    (actualFormed : TypeAdmissible semantic (outer.apply type))
    (expectedFormed : ∀ type ∈ expected, TypeAdmissible semantic (outer.apply type))
    (accepted : Detail.recordExpressionWithExpected context source id type form requirements expected
      state localSchemeInstantiationStart = .ok result) :
    TypeAdmissible semantic (outer.apply result.1.type) ∧
      ∀ row ∈ result.2.requirements, row ∉ state.requirements →
        PredicateAdmissible semantic (TypedTraitResolution.applySubstitution outer row.predicate) := by
  unfold Detail.recordExpressionWithExpected at accepted
  cases fitted : Detail.withExpected context state {id, type} expected with
  | error error => simp [fitted, bind, Except.bind] at accepted
  | ok fit =>
    simp only [fitted, bind, Except.bind, pure, Pure.pure, Except.pure, Except.ok.injEq] at accepted
    subst result
    exact withExpected_normalized_formation formation continuation actualFormed expectedFormed fitted

end Solcore.SourceSemantics.SourceInferenceNormalizedCoercionFormation
